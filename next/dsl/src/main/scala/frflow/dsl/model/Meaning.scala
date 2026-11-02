package frflow.dsl.model

import frflow.core.expr.Binder
import frflow.core.ty.Ty
import frflow.core.vocab.{ModelOp, OpSig}
import frflow.dsl.build.{Declarations, Fault}
import frflow.dsl.flow.ReadRecording
import frflow.dsl.shape.DefineShape
import frflow.dsl.term.{LeanType, Notes}
import frflow.dsl.run.Recorded
import frflow.dsl.vocab.Definition

/** One operation's meaning as a model's body gives it (`inRoom.means(room => …)`): the operation, its inputs' types
  * and their names as written, and its steps over the state, from its inputs' variables.
  */
final case class Meaning(op: Definition[?], inputs: List[LeanType[?]], params: List[String],
    body: Vector[Binder] => Recorded[?]):
  /** Its steps recorded on its inputs' variables, bound at levels `0 … n-1`, with the notes of what they mention. */
  def read: (Notes, ModelOp) =
    val xs = inputs.zipWithIndex.map((t, i) => DefineShape.binder(i, t, params))
    val (steps, notes) = ReadRecording.steps(body(xs.toVector))
    (notes, ModelOp(op.name, xs, Meaning.result(op.leanType.ty), steps))

object Meaning:
  /** An operation known only by assumptions (`op.assumed`): its signature, its inputs named by their types
    * (`account`, `search`); of a Definition that is no operation on a state (`A => Flow[R]`), a fault.
    */
  def assumed(op: Definition[?]): (Notes, Option[OpSig]) = op.leanType.ty match
    case Ty.FlowOf(r, _)               => (Notes.of(Declarations.none), Some(OpSig(op.name, Nil, r)))
    case Ty.FnOf(ps, Ty.FlowOf(r, _)) =>
      (Notes.of(Declarations.none), Some(OpSig(op.name, ps.zipWithIndex.map((t, i) => hint(t, i) -> t), r)))
    case _                             => (Notes.fault(Fault.NotAnOperation(op.name.value)), None)

  private def hint(t: Ty, i: Int): String = t match
    case Ty.Data(n) => n.value.head.toLower.toString + n.value.tail
    case _          => s"x$i"

  /** An operation's result: `R` of its type, `A => Flow[R]` or `Flow[R]`. */
  def result(ty: Ty): Ty = ty match
    case Ty.FnOf(_, Ty.FlowOf(r, _)) => r
    case Ty.FlowOf(r, _)             => r
    case other                       => other
