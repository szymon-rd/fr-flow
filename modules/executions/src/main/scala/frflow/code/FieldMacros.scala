package frflow.code

import frflow.{Call as _, *}
import frflow.dsl.compiled.source.MemberName
import frflow.executions.{Call, Changing, Invocation, Response, World, begun, calledOn, completedBy, itselfMakes}
import frflow.executions.{calledBy as calledByAt, madeBefore, readAs, writtenAs}
import frflow.values.{Obj, Ref, Value}
import scala.quoted.*

// What the words of `Fields.scala` are made of: the macros that read a class's fields, methods and constructor as
// the tree read names them, and the statements they make.

object FieldMacros:
  def readsVals[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Fields.readsAll(${ Expr(vals[C]) }, $on.asValue)(using $st) }

  def givenVals[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Fields.givenAll(${ Expr(vals[C]) }, $on.asValue)(using $st) }

  def constructed[C: Type](on: Expr[Obj[C]], w: Expr[World], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Fields.constructed($on.asValue, ${ Expr(constructor[C]) }, $w)(using $st) }

  def constructedWhenCalled[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Fields.constructedWhenCalled(${ Expr(methods[C]) }, ${ Expr(constructor[C]) }, $on.asValue)(using $st) }

  def calledBy[C: Type](on: Expr[Obj[C]], by: Expr[Term[Value]], w: Expr[World], st: Expr[Stating])(using Quotes)
      : Expr[Term[Boolean]] =
    '{ Fields.calledBy(${ Expr(taking[C]) }, $on.asValue, $by, $w)(using $st) }

  def keeps[C: Type](on: Expr[Obj[C]], kept: Expr[Term[Value]], also: Expr[(Term[Value], World) => Term[Boolean]],
      st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Fields.keeps(${ Expr(taking[C]) }, $on.asValue, $kept, $also)(using $st) }

  /** Each method of the class with how many things it takes. */
  private def taking[C: Type](using Quotes): List[(String, Int)] =
    import quotes.reflect.*
    val found = TypeRepr.of[C].typeSymbol.declaredMethods.filterNot(m =>
      m.isClassConstructor || m.flags.is(Flags.Synthetic))
    if found.isEmpty then report.errorAndAbort(s"${TypeRepr.of[C].show} has no method")
    found.map(m => MemberName.of(m).mkString(" ") -> m.paramSymss.flatten.count(!_.isTypeParam))

  /** The class's constructor with how many things it takes, its methods and its vals, as the tree read names
    * them.
    */
  private def constructor[C: Type](using Quotes): (String, Int) =
    import quotes.reflect.*
    val made = TypeRepr.of[C].typeSymbol.primaryConstructor
    MemberName.of(made).mkString(" ") -> made.paramSymss.flatten.count(!_.isTypeParam)

  private def methods[C: Type](using Quotes): List[String] =
    import quotes.reflect.*
    val found = TypeRepr.of[C].typeSymbol.declaredMethods.filterNot(m =>
      m.isClassConstructor || m.flags.is(Flags.Synthetic))
    if found.isEmpty then report.errorAndAbort(s"${TypeRepr.of[C].show} has no method")
    found.map(MemberName.of(_).mkString(" "))

  private def vals[C: Type](using Quotes): List[String] =
    import quotes.reflect.*
    val once = TypeRepr.of[C].typeSymbol.declaredFields.filterNot(f =>
      f.flags.is(Flags.Mutable) || f.flags.is(Flags.Lazy) || f.flags.is(Flags.Synthetic))
    if once.isEmpty then report.errorAndAbort(s"${TypeRepr.of[C].show} has no val")
    once.map(MemberName.of(_).mkString(" ").trim)

  def madeWhenCalled[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    import quotes.reflect.*
    val of = Expr(MemberName.ofClass(TypeRepr.of[C].typeSymbol))
    '{ Fields.madeWhenCalled(${ Expr(methods[C]) }, $of, $on.asValue)(using $st) }

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

  /** A completed call of the constructor, with as many things as it takes, has returned the object by `w`. */
  def constructed(on: Term[Value], constructor: (String, Int), w: World)(using Stating): Term[Boolean] =
    def taking(left: Int, so: List[Term[Value]]): Term[Boolean] =
      if left == 0 then exists((by: Term[Value], from: Term[BigInt], to: Term[BigInt]) =>
        to <= w && completedBy(make[Invocation](constructor._1, so.reverse.foldRight(Nil: Term[List[Value]])(_ :: _)),
          by, from, make[Response.Returned](on), to))
      else exists((x: Term[Value]) => taking(left - 1, x :: so))
    taking(constructor._2, Nil)

  /** A call of one of the methods on the object, with as many more things as it takes, is made at the moment. */
  def calledBy(methods: List[(String, Int)], on: Term[Value], by: Term[Value], w: World)(using Stating)
      : Term[Boolean] =
    def taking(m: String, left: Int, so: List[Term[Value]]): Term[Boolean] =
      if left == 0 then begun(make[Invocation](m, (on :: so.reverse).foldRight(Nil: Term[List[Value]])(_ :: _)),
        by, w)
      else exists((x: Term[Value]) => taking(m, left - 1, x :: so))
    methods.map((m, n) => taking(m, n, Nil)).reduce(_ || _)

  def keeps(methods: List[(String, Int)], on: Term[Value], kept: Term[Value],
      also: (Term[Value], World) => Term[Boolean])(using Stating): Term[Boolean] =
    forall((method: Term[String], rest: Term[List[Value]], by: Term[Value], w: Term[BigInt]) =>
      calledByAt(make[Invocation](method, kept :: rest), by, w) implies exists((i: Term[BigInt]) =>
        itselfMakes(make[Invocation](method, kept :: rest), by, i, w) && (calledBy(methods, on, by, i) || also(by, i))))

  def givenAll(names: List[String], on: Term[Value])(using Stating): Term[Boolean] =
    names.map(n => writtenAs(on, n, heldIn(n, on))).reduce(_ && _)

  def constructedWhenCalled(methods: List[String], constructor: (String, Int), on: Term[Value])(using Stating)
      : Term[Boolean] =
    forall((w: Term[BigInt]) =>
      methods.map(m => calledOn(on, m, w)).reduce(_ || _) implies constructed(on, constructor, w))
