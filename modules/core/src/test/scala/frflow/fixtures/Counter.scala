package frflow.fixtures

import frflow.dsl.*

/** Whether the counter accepts increments. */
enum Mode:
  case Counting, Frozen

/** Abstract counter.
  * @param n current value
  */
final case class Bounded(n: Int)

/** Counter with a configurable cap.
  * @param n    current value
  * @param cap  configured maximum
  * @param mode whether increments are accepted
  */
final case class Register(n: Int, cap: Int, mode: Mode):
  /** Whether an increment is allowed. */
  def canInc: Boolean = mode == Mode.Counting && n < cap

object Limits:
  /** The bound of the requirement. */
  val Max: Int = 10

object CounterTheory extends Theory("Counter"):
  domain[(Mode, Register)]
  val E1 = assumption("E1", "CapConfigured", "The configured cap is positive.", "Set by deployment configuration.")
  law("MaxPositive", "The bound is positive.")(Limits.Max > 0)

object C0
    extends Requirements[Bounded](CounterTheory, "C0", "Bounded",
      statement = "The counter never exceeds the bound.", rationale = "Simplest bounded resource."):
  init(s => s.n == 0)
  val inc = operation[Unit]("inc", "Add one.").check((s, _) => s.n < Limits.Max).act((s, _) => s.copy(n = s.n + 1))
  val reset = operation[Unit]("reset", "Back to zero.").act((_, _) => Bounded(0))
  requirement("LeMax", "The counter is at most the bound.")(s => s.n <= Limits.Max)

object C1
    extends Implementation[Register, Bounded](C0, "C1", "CapRegister",
      statement = "The counter stays below a configured cap of at most the bound.", rationale = "Makes the bound configurable."):
  assumes(CounterTheory.E1)
  abstraction(s => Bounded(s.n))
  glue(s => s.cap <= Limits.Max)
  initial(Register(0, Limits.Max, Mode.Counting))
  val inc = operation[Unit]("inc", "Add one if allowed.")
    .assume(CounterTheory.E1)((s, _) => s.cap > 0)
    .check((s, _) => s.canInc)
    .act((s, _) => s.copy(n = s.n + 1))
    .refines(C0.inc)((_, _) => ())
  val reset = operation[Unit]("reset").act((s, _) => s.copy(n = 0)).refines(C0.reset)((_, _) => ())
  val freeze = operation[Unit]("freeze", "Stop accepting increments.").act((s, _) => s.copy(mode = Mode.Frozen)).refinesSkip

object CounterModel extends Model(CounterTheory, C0, C1)
