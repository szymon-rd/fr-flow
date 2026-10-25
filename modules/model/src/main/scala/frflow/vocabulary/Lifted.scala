package frflow
package vocabulary

import frflow.types.Shape

/** A lambda over terms (or a term), with its Lean and its Scala: built when first used, after every val of the model
  * is set, so a model may name a `define` declared below it.
  */
final class Lifted[+F] private[frflow] (build: () => (List[Binder], Term[?]), private[frflow] val fn: AnyRef | Null, val source: String,
    asValue: Boolean = false, runs: Lifted[?] | Null = null):
  private[frflow] lazy val built = Building(build())
  private lazy val printed: Printed = LeanPrinter().print(built._1, built._2.termTree, built._2.termType)
  private lazy val compiled: AnyRef = Eval.function(built._1, built._2.termTree)
  /** The Scala function; a term defined as a value (`onShelf := shelf.length`), its value under the bindings in force. */
  def value: F = (if runs != null then runs.value else if asValue then compiled.asInstanceOf[() => Any]() else compiled).asInstanceOf[F]
  /** The same Lean, run by another's Scala: how a test injects a translation bug. */
  private[frflow] def runningAs(other: Lifted[?]): Lifted[F] = Lifted(build, fn, source, asValue, other)
  def params: List[(String, String)] = printed.params
  def result: String = printed.result
  def body: String = printed.body
  def types: List[TypeDecl] = printed.types
  def opaques: List[String] = printed.opaques.map(o => Names.ident(o.name))
  def paramRefs: List[(String, String)] = printed.paramRefs
  def defs: List[Def[?]] = printed.defs
  def paramObjects: List[Param[?]] = printed.paramObjects
  def opaqueObjects: List[Opaque] = printed.opaques
  /** The boundaries a flow calls, and whether it mentions the boundaries' world. */
  def boundaries: List[Boundary[?]] = printed.boundaries
  def world: Boolean = printed.world
  /** The error types a flow raises or handles (Lean's `[MonadExceptOf E m]`). */
  def errors: List[String] = printed.errors
  /** The branches a flow runs at once, each with what its proof must show (that they commute). */
  private[frflow] def commutes: List[Commute] = printed.commutes
  def lean: String = if params.isEmpty then body else s"fun ${params.map((n, t) => s"($n : $t)").mkString(" ")} => $body"
  def leanType: String = (params.map(_._2) :+ result).mkString(" → ")

object Lifted:
  /** A term, built when first used. */
  @scala.annotation.publicInBinary private[frflow] def thunk(t: () => Term[?], source: String): Lifted[() => Any] = Lifted(() => (Nil, t()), null, source)
  /** A term defined as a value. */
  @scala.annotation.publicInBinary private[frflow] def term(t: () => Term[?], source: String): Lifted[Any] = Lifted(() => (Nil, t()), null, source, asValue = true)
  /** A flow from its input: its steps. */
  @scala.annotation.publicInBinary private[frflow] def flow(f: AnyRef, ins: List[LeanType[?]], source: String): Lifted[Nothing] =
    Lifted(() => {
      val bs = Lambda.binders(f, ins)
      val (s, t) = Steps.of(Fn.call(f, bs.map(_.term[Any])).asInstanceOf[Flow[?]])
      (bs, Term(Tree.Do(s), t))
    }, f, source)
  /** The code of a flow's contract: the flow from its inputs, run on the models from a world. */
  @scala.annotation.publicInBinary private[frflow] def runOn(flow: Def[?], ins: List[LeanType[?]], result: LeanType[?],
      err: Option[LeanType[?]] = None): Lifted[Nothing] =
    Lifted(() => {
      val hints = flow.lifted.built._1.map(_.hint)
      val as = ins.zipWithIndex.map((t, i) => Binder(hints.lift(i).getOrElse(if i == 0 then "x" else s"x$i"), t))
      val w = Binder("w", summon[LeanType[World]])
      // A run that may fail gives its outcome: `Except E R`, and the world after.
      val r = (err, result.shape) match
        case (Some(e), Shape.TupleOf(List(x, world))) => LeanType.of(Shape.TupleOf(List(LeanType.of(Shape.EitherOf(e, x)), world)))
        case _                                        => result
      (as :+ w, Term(Tree.RunOn(Tree.Call(flow, as.map(Tree.Var(_))), Tree.Var(w), err), r))
    }, null, flow.lifted.source)
  /** A lambda over terms of these types. */
  @scala.annotation.publicInBinary private[frflow] def lambda[F](f: AnyRef, types: List[LeanType[?]], source: String): Lifted[F] =
    Lifted(() => { val bs = Lambda.binders(f, types); (bs, Lambda.body(f, bs)) }, f, source)
