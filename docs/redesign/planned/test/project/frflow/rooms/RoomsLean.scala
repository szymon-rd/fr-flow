package rooms

import frflow.core.expr.Lambda
import frflow.core.name.{KbName, TypeName}
import frflow.core.spec.{CallForm, Form, Statement, Written}
import frflow.core.ty.DataType
import frflow.dsl.build.Deferred
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.{LowerEnv, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.{Printed, Scope}

/** The rooms model's parts as Lean, printed from their terms (`Printed`), each elaborated first. */
object RoomsLean:
  private val booking = DataType.Product(TypeName("Booking"), "rooms.Booking", Nil)
  val env: LowerEnv = LowerEnv(KbName("Rooms"), _ => Nil, _ => Names.builtin("database"),
    _ => Names.builtin("Database"), n => Option.when(n == booking.typeName)(booking))
  val naming: Naming = Naming.over(Set("granted"), Set("Booking"))
  val scope: Scope = Scope(0, naming)

  def elaborated[A](d: Deferred[A]): A = d.run.fold(e => throw AssertionError(e.toString), _._2)

  /** A define's written lambda: what the Definition `define` made carries. */
  def lambda(d: frflow.dsl.vocab.Definition[?]): Deferred[Written[Lambda]] =
    d.onTheSpot.fold(throw AssertionError(s"${d.name.value} is not a define"))(_.lambda)

  /** The call (or run) a statement reads as, and its post. */
  def call(s: Deferred[Statement]): CallForm = elaborated(s).call.getOrElse(throw AssertionError("reads as no call"))
  def post(s: Deferred[Statement]): Written[Lambda] = call(s).posted

  /** A golden file of `test/proof/resources/rooms`, compiled by Lean (`r43-spike/rooms-lean`). */
  def golden(name: String): String =
    scala.io.Source.fromResource(s"rooms/$name", getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  /** A formula's Lean. */
  def formula(w: Written[?]): String = w.form match
    case Form.Term(t)  => Print.expr(Printed.formula(env, naming)(t.run))
    case Form.Steps(_) => throw AssertionError("a program's steps, not a formula")

  /** A lambda's Lean as its `def`: its inputs, then its body over them. */
  def define(w: Written[Lambda]): String = w.form match
    case Form.Term(t)  =>
      val (inputs, body) = Printed.define(env, naming)(w.value.params, t.run)
      s"${Print.binders(inputs)} := ${Print.expr(body)}"
    case Form.Steps(_) => throw AssertionError("a program's steps")
