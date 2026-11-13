package frflow.dsl.compiled

import frflow.dsl.term.{Branch, Cases, Data, Terms}
import frflow.dsl.term.Term as DTerm

/** A `match` in a compiled class: on an enum, one arm per case, each binding the case's fields
  * (`case Circle(r) =>`) or the case (`case c: Circle =>`), a last `case _ =>` standing for every case not
  * written; on an option, `Some(x)` and `None`. No guard, no pattern inside a pattern: the prover's match has the same
  * arms, and misses none.
  */
private[compiled] trait CompileMatch extends Compiling:
  this: Compiler =>
  import q.reflect.*

  /** One arm: its case's type, what its pattern binds of the case's fields, in order, or of the case itself. */
  private final case class Arm(of: TypeRepr, fields: List[Option[Symbol]], whole: Option[Symbol], body: Term)

  def matched(on: Term, cases: List[CaseDef], as: TypeRepr)(using Env): DTerm[Any] =
    cases.find(_.guard.nonEmpty).foreach(c => refuse("a case with a guard: write the `if` in the case's body", c))
    val s = on.tpe.widen
    if elementOf(s, OptionClass).nonEmpty then optional(on, cases, as)
    else if s.typeSymbol.children.nonEmpty then
      Cases[Any, Any](read(on, s), arms(s, cases, on).map(branch(s, _, as)))(using spec(as, on))
    else refuse(s"a match on a ${s.show}: an enum's cases and an option's are matched", on)

  private def optional(on: Term, cases: List[CaseDef], as: TypeRepr)(using env: Env): DTerm[Any] =
    val none = cases.collectFirst { case CaseDef(p: Term, _, body) if names(p, TypeRepr.of[None.type]) => body }
    val some = cases.collectFirst { case CaseDef(SomeOf(x), _, body) => (x, body) }
    (none, some, elementOf(on.tpe, OptionClass)) match
      case (Some(n), Some((x, body)), Some(a)) if cases.size == 2 =>
        val hint = x.fold("x")(_.name)
        val held = once(List((hint, spec(a, on))))(ys => read(body, as)(using env ++ x.map((_, ys.head)).toList))
        Terms.foldOption[Any, Any](read(on, on.tpe.widen).asInstanceOf[DTerm[Option[Any]]], read(n, as), hint)(y =>
          held(List(y)))(using spec(a, on))
      case _                                                       =>
        refuse("a match on an option that is not one case of `Some(x)` and one of `None`", on)

  /** `Some(x)` or `Some(_)`: what it binds. */
  private object SomeOf:
    def unapply(p: Tree): Option[Option[Symbol]] = p match
      case TypedOrTest(inner, _)                                      => unapply(inner)
      case Unapply(fun, _, List(x)) if fun.symbol.owner == SomeObject => bound(x)
      case _                                                          => None

  /** What one position of a pattern binds: a variable, or nothing (`_`); none of a pattern inside it. */
  private def bound(p: Tree): Option[Option[Symbol]] = p match
    case b @ Bind(_, Wildcard()) => Some(Some(b.symbol))
    case Wildcard()              => Some(None)
    case _                       => None

  /** An arm for each case of the enum, in its order: the one written for it, or the default's. */
  private def arms(s: TypeRepr, cases: List[CaseDef], on: Term): List[Arm] =
    val written = cases.map(c => arm(c).toRight(c.rhs))
    val default = written.collectFirst { case Left(body) => body }
    s.typeSymbol.children.map { child =>
      val of = if child.isClassDef then child.typeRef else child.termRef
      written.collectFirst { case Right(a) if a.of.typeSymbol == of.typeSymbol && a.of.termSymbol ==
        of.termSymbol => a.copy(of = of) }.orElse(default.map(Arm(of, Nil, None, _)))
        .getOrElse(refuse(s"a match that misses the case ${child.name}", on))
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
    case other                                     =>
      refuse("this pattern: a case's fields or the case are bound", other)

  private def fields(ps: List[Tree], c: CaseDef): List[Option[Symbol]] =
    ps.map(p => bound(p).getOrElse(refuse("a pattern inside a pattern: bind the field and match it in the body", c)))

  /** The arm as the term language has it: the case told from a value of the enum, and the arm's body over the
    * case's term, each variable its pattern binds the case's field read by its selector, or the case.
    */
  private def branch(sum: TypeRepr, a: Arm, as: TypeRepr)(using env: Env): Branch[Any, ?, Any] =
    val (whole, made) = (spec(sum, a.body), caseOf(a.of, a.body))
    val caseType = Data.caseType[Any, Any](whole, made.fields)
    val hint = made.label.toLowerCase
    val body = once(List((hint, caseType))) { cs =>
      val named = made.fields.zip(a.fields).collect { case (f, Some(x)) => (x, DTerm.select(cs.head, f)) }
      read(a.body, as)(using env ++ named ++ a.whole.map((_, cs.head)).toList)
    }
    Branch[Any, Any, Any](Data.caseOf[Any, Any](whole, made.label, made.fields, made.told), hint, caseType, c =>
      body(List(c)))
