package frflow.code

import frflow.{Call as _, *}
import frflow.dsl.compiled.source.MemberName
import frflow.executions.{Call, Changing, World, calledOn, madeBefore, readAs}
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

extension [C](on: Obj[C])
  /** The object has been made, of its class, before the moment: by the code read. */
  inline def isMade(w: World)(using st: Stating): Term[Boolean] = ${ FieldMacros.made[C]('on, 'w, 'st) }

  /** Every read of the field finds what it holds (`field`): what Scala says of a `val`. */
  inline def readsAsHeld(inline name: String)(using st: Stating): Term[Boolean] =
    ${ FieldMacros.reads[C]('on, 'name, 'st) }

  /** Every read of a `val` of the object's class finds what it holds: each field the class assigns once. */
  inline def readsItsValsAsHeld(using st: Stating): Term[Boolean] = ${ FieldMacros.readsVals[C]('on, 'st) }

  /** A method of the object's class is called on it only once it has been made. */
  inline def isMadeWhenCalled(using st: Stating): Term[Boolean] = ${ FieldMacros.madeWhenCalled[C]('on, 'st) }

  /** A call of the method of the object's class named `name`, given `arguments`: a statement may name a method
    * code outside the class may not (`h.method[Unit]("assertNotShuttingDown")`).
    */
  inline def method[A](inline name: String, arguments: Term[Value]*): Call[A] =
    ${ FieldMacros.method[C, A]('on, 'name, 'arguments) }

object FieldMacros:
  def readsVals[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    import quotes.reflect.*
    val once = TypeRepr.of[C].typeSymbol.declaredFields.filterNot(f =>
      f.flags.is(Flags.Mutable) || f.flags.is(Flags.Lazy) || f.flags.is(Flags.Synthetic))
    if once.isEmpty then report.errorAndAbort(s"${TypeRepr.of[C].show} has no val")
    val named = Expr(once.map(MemberName.of(_).mkString(" ").trim))
    '{ Fields.readsAll($named, $on.asValue)(using $st) }

  def madeWhenCalled[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    import quotes.reflect.*
    val cls = TypeRepr.of[C].typeSymbol
    val methods = cls.declaredMethods.filterNot(m => m.isClassConstructor || m.flags.is(Flags.Synthetic))
    if methods.isEmpty then report.errorAndAbort(s"${TypeRepr.of[C].show} has no method")
    val named = Expr(methods.map(MemberName.of(_).mkString(" ")))
    val of = Expr(MemberName.ofClass(cls))
    '{ Fields.madeWhenCalled($named, $of, $on.asValue)(using $st) }

  def method[C: Type, A: Type](on: Expr[Obj[C]], name: Expr[String], arguments: Expr[Seq[Term[Value]]])(
      using Quotes): Expr[Call[A]] =
    import quotes.reflect.*
    val named = TypeRepr.of[C].typeSymbol.declaredMethod(name.valueOrAbort) match
      case List(one) => Expr(MemberName.of(one).mkString(" "))
      case found => report.errorAndAbort(s"${TypeRepr.of[C].show} has ${found.size} methods ${name.valueOrAbort}")
    '{ Call.of[A]($named, ($on.asValue +: $arguments)*) }

  def made[C: Type](on: Expr[Obj[C]], w: Expr[World], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    import quotes.reflect.*
    val cls = Expr(MemberName.ofClass(TypeRepr.of[C].typeSymbol))
    '{ Fields.made($on.asValue, $cls, $w)(using $st) }

  def reads[C: Type](on: Expr[Obj[C]], name: Expr[String], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    val named = Expr(label[C](name))
    '{ Fields.reads($named, $on.asValue)(using $st) }

  /** The field as the tree read names it: its class and its name. */
  private def label[C: Type](name: Expr[String])(using Quotes): String =
    import quotes.reflect.*
    val member = TypeRepr.of[C].typeSymbol.fieldMember(name.valueOrAbort)
    if !member.exists then report.errorAndAbort(s"${TypeRepr.of[C].show} has no field ${name.valueOrAbort}")
    MemberName.of(member).mkString(" ").trim

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

  def made(on: Term[Value], cls: String, w: World)(using Stating): Term[Boolean] = madeBefore(on, cls, w)

  def readsAll(names: List[String], on: Term[Value])(using Stating): Term[Boolean] =
    names.map(reads(_, on)).reduce(_ && _)

  def madeWhenCalled(methods: List[String], cls: String, on: Term[Value])(using Stating): Term[Boolean] =
    forall((w: Term[BigInt]) =>
      methods.map(m => calledOn(on, m, w)).reduce(_ || _) implies madeBefore(on, cls, w))

  def reads(name: String, on: Term[Value])(using Stating): Term[Boolean] = readAs(on, name, heldIn(name, on))
