package frflow.dsl.term

import frflow.core.term.Constructor
import scala.quoted.*

/** The macros of the terms built from a type's parts, each checked at compile time against the type: an arm of a match
  * (`.on[Case](fields => …)`), a value made from its fields (`make[Booking](r, s, e)`), a record with one field
  * replaced (`b.updated(_.start, t)`). The code they write is typed: no cast.
  */
object CaseMacros:
  /** An arm over case `C` of `S`: its test, its variable's type, and the developer's function of the case's fields,
    * each read by its selector.
    */
  def branch[S: Type, C: Type, R: Type](f: Expr[Any])(using Quotes): Expr[Branch[S, C, R]] =
    import quotes.reflect.report
    val label = DataMacros.names[C]._2
    val sum = Expr.summon[LeanType[S]].getOrElse(report.errorAndAbort(s"no LeanType for ${Type.show[S]}"))
    '{
      given caseType: LeanType[C] = Data.caseType[S, C]($sum, ${ DataMacros.fields[C] })
      Branch[S, C, R](Data.caseOf[S, C]($sum, ${ Expr(label) }, caseType.fields, s => s match
        case c: C => Some(c)
        case _    => None), ${ Expr(label.toLowerCase) }, caseType, (c: Term[C]) => ${ applied[C, R](f, 'c) })
    }

  /** The developer's function applied to the case's fields (a term for a case without any). */
  private def applied[C: Type, R: Type](f: Expr[Any], c: Expr[Term[C]])(using Quotes): Expr[Term[R]] =
    import quotes.reflect.{asTerm, Select}
    val args = DataMacros.fieldsOf[C].zipWithIndex.map { case ((n, t), i) => t.asType match
      case '[x] => '{ Term.select($c, ${ DataMacros.typedField[C, x](n, i) }) }.asTerm }
    if args.isEmpty then f.asExprOf[Term[R]] else Select.overloaded(f.asTerm, "apply", Nil, args).asExprOf[Term[R]]

  /** `C` made from its fields' terms, each checked against its field's type; an enum's case is a term of the enum. */
  def make[C: Type](args: Expr[Seq[Term[?]]])(using Quotes): Expr[Term[?]] =
    import quotes.reflect.{report, TypeRepr}
    val given_ = args match
      case Varargs(as) => as.toList
      case _           => report.errorAndAbort("make takes its fields' terms, written out")
    val fs = DataMacros.fieldsOf[C]
    if fs.size != given_.size then report.errorAndAbort(s"${Type.show[C]} has ${fs.size} fields, given ${given_.size}")
    val whole = DataMacros.sumOf[C].getOrElse(TypeRepr.of[C])
    whole.asType match
      case '[w] =>
        val ctor = DataMacros.constructor[C, w] match
          case '{ $c: Constructor[f] } => '{ Term.construct[f]($c)(using ${ leanType[f] }) }
        given_.zip(fs).foldLeft[Expr[Term[?]]](ctor)((f, a) => appliedTo(f, a._1, a._2._1))

  /** One more field given to a constructor's term: `Term.app`, after checking the field's type. */
  private def appliedTo(f: Expr[Term[?]], a: Expr[Term[?]], name: String)(using Quotes): Expr[Term[?]] =
    import quotes.reflect.{asTerm, report, TypeRepr}
    f match
      case '{ $g: Term[x => r] } =>
        if !(a.asTerm.tpe <:< TypeRepr.of[Term[x]]) then
          report.errorAndAbort(s"field $name is a ${Type.show[x]}, given a ${a.asTerm.tpe.widen.show}", a)
        '{ Term.app[x, r]($g, ${ a.asExprOf[Term[x]] })(using ${ leanType[r] }) }
      case _ => report.errorAndAbort("FrFlow bug: a constructor's term is not a function")

  /** `t` with the field `pick` reads replaced by `v`: the field's selector derived here, typed by the field. */
  def updated[A: Type, F: Type](t: Expr[Term[A]], pick: Expr[Term[A] => Term[F]], v: Expr[Term[F]])(using Quotes)
      : Expr[Term[A]] =
    import quotes.reflect.{asTerm, report}
    val name = picked(pick.asTerm).getOrElse(report.errorAndAbort("updated takes a field: `_.start`", pick))
    val i = DataMacros.fieldsOf[A].indexWhere(_._1 == name)
    if i < 0 then report.errorAndAbort(s"${Type.show[A]} has no field $name", pick)
    '{ Term.copy($t, ${ DataMacros.typedField[A, F](name, i) }.selector, $v) }

  private def leanType[X: Type](using Quotes): Expr[LeanType[X]] =
    Expr.summon[LeanType[X]].getOrElse(quotes.reflect.report.errorAndAbort(s"no LeanType for ${Type.show[X]}"))

  /** The field name in `_.start` (`selectDynamic("start")`). */
  private def picked(using Quotes)(t: quotes.reflect.Term): Option[String] =
    import quotes.reflect.*
    t match
      case Inlined(_, _, b)                                   => picked(b)
      case Block(List(DefDef(_, _, _, Some(b))), _)           => picked(b)
      case Block(Nil, b)                                      => picked(b)
      case Typed(b, _)                                        => picked(b)
      case TypeApply(Select(b, _), _)                         => picked(b)
      case Apply(Select(_, "selectDynamic"), List(Literal(StringConstant(n)))) => Some(n)
      case _                                                  => None
