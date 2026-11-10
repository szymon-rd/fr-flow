package frflow.dsl.lifted

import frflow.dsl.term.{CaseMacros, DataMacros}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** A domain type's values in lifted code: a case class's or an enum case's value made from its fields
  * (`Booking(room, start, end)`), a field read (`b.start`), a copy with fields replaced (`b.copy(end = e)`), and an
  * enum's case without fields named (`Shape.Empty`). Each is the term a model writes with `make`, a field's
  * selector and `updated`.
  */
private[lifted] trait ReadData extends Reading:
  this: Reader =>
  import q.reflect.*

  /** `C(…)` or `new C(…)` of a case class `C` with no type parameters. */
  def record(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    val cls = c.on match
      case New(tpt) if c.name == "<init>" => tpt.tpe.typeSymbol
      case on if c.name == "apply"        => on.tpe.termSymbol.companionClass
      case _                              => Symbol.noSymbol
    Option.when(isRecord(cls))(construct(cls, c.args, c.whole))

  private def isRecord(cls: Symbol): Boolean =
    !cls.isNoSymbol && cls.flags.is(Flags.Case) && cls.typeRef.typeArgs.isEmpty && cls.typeMembers.forall(m =>
      !m.isTypeParam)

  private def construct(cls: Symbol, args: List[Term], at: Term)(using Env)(using Quotes): Expr[DTerm[?]] =
    val fields = fieldsOf(cls.typeRef)
    if fields.size != args.size then refuse(s"${cls.name} made from ${args.size} of its ${fields.size} fields", at)
    cls.typeRef.asType match
      case '[c] => CaseMacros.make[c](Varargs(args.zip(fields).map((a, f) => read(a, f._2))))

  def caseValue(t: Term)(using Quotes): Expr[DTerm[?]] = t.symbol.termRef.asType match
    case '[c] => CaseMacros.make[c](Varargs(Nil))

  def field(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    val own = c.on.tpe.widen
    val i = fieldsOf(own).indexWhere(_._1 == c.name)
    if c.name == "copy" && isRecord(own.typeSymbol) then Some(copied(c, own))
    else Option.when(c.args.isEmpty && i >= 0 && own.typeSymbol.flags.is(Flags.Case))(selected(c, i))

  private def selected(c: Calling, i: Int)(using Env)(using Quotes): Expr[DTerm[?]] =
    (c.on.tpe.widen.asType, c.own.asType) match
      case ('[r], '[f]) => '{ DTerm.select(${ readAs[r](c.on) }, ${ DataMacros.typedField[r, f](c.name, i) }) }
      case _            => refuse(s"the field ${c.name}", c.whole)

  /** `b.copy(end = e)`: each field given replaced, in the order given; one left as it is (the compiler's default
    * for it) kept.
    */
  private def copied(c: Calling, own: TypeRepr)(using Env)(using Quotes): Expr[DTerm[?]] = own.asType match
    case '[r] =>
      val fields = fieldsOf(own)
      val given_ = c.args.zipWithIndex.map {
        case (NamedArg(name, value), _) => (fields.indexWhere(_._1 == name), value)
        case (value, i)                 => (i, value)
      }.filterNot((_, value) => unchanged(value))
      given_.foldLeft(readAs[r](c.on)) { case (t, (i, value)) =>
        fields(i)._2.asType match
          case '[x] =>
            '{ DTerm.copy($t, ${ DataMacros.typedField[r, x](fields(i)._1, i) }.selector, ${ readAs[x](value) }) }
      }
