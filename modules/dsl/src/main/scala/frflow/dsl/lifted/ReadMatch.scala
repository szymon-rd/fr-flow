package frflow.dsl.lifted

import frflow.dsl.term.{Branch, Cases, Data, DataMacros, LeanType, Terms}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** A `match` in lifted code: on an enum, one arm per case, each binding the case's fields (`case Circle(r) =>`) or
  * the case (`case c: Circle =>`), a last `case _ =>` standing for every case not written; on an option, `Some(x)`
  * and `None`. No guard, no pattern inside a pattern: Lean's match has the same arms, and misses none.
  */
private[lifted] trait ReadMatch extends Reading:
  this: Reader =>
  import q.reflect.*

  /** One arm: its case's type, what its pattern binds of the case's fields, in order, or of the case itself. */
  private final case class Arm(of: TypeRepr, fields: List[Option[Symbol]], whole: Option[Symbol], body: Term)

  def matched(on: Term, cases: List[CaseDef], as: TypeRepr)(using Env)(using Quotes): Expr[DTerm[?]] =
    cases.find(_.guard.nonEmpty).foreach(c => refuse("a case with a guard: write the `if` in the case's body", c))
    val s = on.tpe.widen
    if elementOf(s, OptionClass).nonEmpty then optional(on, cases, as)
    else if s.typeSymbol.children.nonEmpty then (s.asType, as.asType) match
      case ('[s], '[r]) => '{ Cases[s, r](${ readAs[s](on) }, ${ Expr.ofList(arms[s, r](s, cases, on)) })(
        using ${ spec[r](on) }) }
      case _            => refuse("this match", on)
    else refuse(s"a match on a ${s.show}: an enum's cases and an option's are matched", on)

  private def optional(on: Term, cases: List[CaseDef], as: TypeRepr)(using env: Env)(using Quotes): Expr[DTerm[?]] =
    val none = cases.collectFirst { case CaseDef(p: Term, _, body) if names[None.type](p) => body }
    val some = cases.collectFirst { case CaseDef(SomeOf(x), _, body) => (x, body) }
    (none, some, elementOf(on.tpe, OptionClass).map(_.asType), as.asType) match
      case (Some(n), Some((x, body)), Some('[a]), '[r]) if cases.size == 2 =>
        '{ Terms.foldOption[a, r](${ readAs[Option[a]](on) }, ${ readAs[r](n) }, ${ Expr(x.fold("x")(_.name)) })(
          (y: DTerm[a]) => ${ readAs[r](body)(using env ++ x.map((_, 'y)).toList) })(using ${ spec[a](on) }) }
      case _                                                                =>
        refuse("a match on an option that is not one case of `Some(x)` and one of `None`", on)

  /** `Some(x)` or `Some(_)`: what it binds. */
  private object SomeOf:
    def unapply(p: Tree): Option[Option[Symbol]] = p match
      case TypedOrTest(inner, _)                                  => unapply(inner)
      case Unapply(fun, _, List(x)) if fun.symbol.owner == SomeObject => bound(x)
      case _                                                      => None

  /** What one position of a pattern binds: a variable, or nothing (`_`); none of a pattern inside it. */
  private def bound(p: Tree): Option[Option[Symbol]] = p match
    case b @ Bind(_, Wildcard()) => Some(Some(b.symbol))
    case Wildcard()              => Some(None)
    case _                       => None

  /** An arm for each case of the enum, in its order: the one written for it, or the default's. */
  private def arms[S: Type, R: Type](s: TypeRepr, cases: List[CaseDef], on: Term)(using Env)(using Quotes)
      : List[Expr[Branch[S, ?, R]]] =
    val written = cases.map(c => arm(c).toRight(c.rhs))
    val default = written.collectFirst { case Left(body) => body }
    s.typeSymbol.children.map { child =>
      val of = if child.isClassDef then child.typeRef else child.termRef
      val a = written.collectFirst { case Right(a) if a.of.typeSymbol == of.typeSymbol && a.of.termSymbol ==
        of.termSymbol => a }.orElse(default.map(Arm(of, Nil, None, _)))
        .getOrElse(refuse(s"a match that misses the case ${child.name}", on))
      of.asType match
        case '[c] => branch[S, c, R](a)
    }

  /** A written arm, or none of the default (`case _ =>`). */
  private def arm(c: CaseDef): Option[Arm] = c.pattern match
    case Wildcard()                                => None
    case p: Term if isEnumValue(p)                 => Some(Arm(p.symbol.termRef, Nil, None, c.rhs))
    case TypedOrTest(Unapply(_, _, ps), tpt)       => Some(Arm(tpt.tpe, fields(ps, c), None, c.rhs))
    case Unapply(fun, _, ps)                       =>
      Some(Arm(fun.symbol.owner.companionClass.typeRef, fields(ps, c), None, c.rhs))
    case b @ Bind(_, Typed(_, tpt))                => Some(Arm(tpt.tpe, Nil, Some(b.symbol), c.rhs))
    case b @ Bind(_, TypedOrTest(Wildcard(), tpt)) => Some(Arm(tpt.tpe, Nil, Some(b.symbol), c.rhs))
    case Typed(_, tpt)                             => Some(Arm(tpt.tpe, Nil, None, c.rhs))
    case other                                     => refuse("this pattern: a case's fields or the case are bound", other)

  private def fields(ps: List[Tree], c: CaseDef): List[Option[Symbol]] =
    ps.map(p => bound(p).getOrElse(refuse("a pattern inside a pattern: bind the field and match it in the body", c)))

  private def branch[S: Type, C: Type, R: Type](a: Arm)(using env: Env)(using Quotes): Expr[Branch[S, ?, R]] =
    val label = DataMacros.names[C]._2
    '{
      given caseType: LeanType[C] = Data.caseType[S, C](${ spec[S](a.body) }, ${ DataMacros.fields[C] })
      Branch[S, C, R](Data.caseOf[S, C](${ spec[S](a.body) }, ${ Expr(label) }, caseType.fields, s => s match
        case c: C => Some(c)
        case _    => None), ${ Expr(label.toLowerCase) }, caseType, (c: DTerm[C]) => ${ body[C, R](a, 'c) })
    }

  /** The arm's body, each variable its pattern binds the case's field read by its selector, or the case. */
  private def body[C: Type, R: Type](a: Arm, c: Expr[DTerm[C]])(using env: Env)(using Quotes): Expr[DTerm[R]] =
    val named = fieldsOf(TypeRepr.of[C]).zipWithIndex.zip(a.fields).collect { case (((name, ty), i), Some(x)) =>
      ty.asType match
        case '[f] => (x, '{ DTerm.select($c, ${ DataMacros.typedField[C, f](name, i) }) })
    }
    readAs[R](a.body)(using env ++ named ++ a.whole.map((_, c)).toList)
