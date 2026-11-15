package frflow.code

import frflow.*
import frflow.dsl.compiled.source.MemberName
import frflow.executions.Changing
import frflow.values.{Obj, Ref, Value}
import scala.quoted.*

// What an object holds. A field is named as the tree read from its class's TASTy names it; what it holds is a
// value of the code. A statement may name a field code outside the class may not.

/** What a field that is assigned once holds, of an object. */
val heldIn = Declaration[(String, Value) => Value]("what a field that is assigned once holds, of an object")

/** What a field that is assigned again holds, of an object at a moment. */
val heldAt = Declaration[(String, Value, BigInt) => Value]("what a field holds, of an object at a moment")

extension [C](on: Obj[C])
  /** The field of the object named `name`: of a `val`, what it holds (`h.field("threads")`); of a `var`, what it
    * holds at each moment (`h.field("count").at(w)`).
    */
  transparent inline def field(inline name: String)(using st: Stating): Any =
    ${ FieldMacros.field[C]('on, 'name, 'st) }

object FieldMacros:
  def field[C: Type](on: Expr[Obj[C]], name: Expr[String], st: Expr[Stating])(using Quotes): Expr[Any] =
    import quotes.reflect.*
    val cls = TypeRepr.of[C]
    val member = cls.typeSymbol.fieldMember(name.valueOrAbort)
    if !member.exists then report.errorAndAbort(s"${cls.show} has no field ${name.valueOrAbort}")
    val named = Expr(MemberName.of(member).mkString(" ").trim)
    cls.memberType(member).widen.asType match
      case '[f] =>
        if member.flags.is(Flags.Mutable) then '{ Fields.changing[f]($named, $on.asValue)(using $st) }
        else '{ Fields.constant[f]($named, $on.asValue)(using $st) }

/** What the macro makes: a field's value as a term, read through the two words. */
object Fields:
  def constant[F](name: String, on: Term[Value])(using Stating): Obj[F] =
    heldIn(name, on).asInstanceOf[Obj[F]]

  def changing[F](name: String, on: Term[Value])(using Stating): Changing[Ref[F]] =
    new Changing(w => heldAt(name, on, w).asInstanceOf[Obj[F]])
