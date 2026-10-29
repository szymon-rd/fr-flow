package whole

import frflow.*
import frflow.core.analysis.Problem
import frflow.proof.layout.Laid
import frflow.proof.lean.print.Print
import rooms.Booking

/** The review's probes on the whole pipeline (elaborated, validated, laid out): no false statement prints as a
  * tautology, and a FrModel named as a record is refused.
  */
class CaptureSuite extends munit.FunSuite:
  /** A Declaration named as Lean's `some`, which Lean spells `some_`, beside a binder named `some_`. */
  private val some = Declaration[BigInt]("a number, named as Lean's some")
  private val everyIsSome =
    Node.claim("Every number is some.")(forall((some_ : Term[BigInt]) => some_ === some.term))

  /** A binder named as the FrModel, beside a call of one of its defines. */
  private val positive = define { (n: Term[BigInt]) => n > 0 }
  private val everyIsPositive =
    Node.claim("Every number is positive.")(forall((Probe: Term[BigInt]) => positive(Probe)))

  /** A binder named as a Declaration it mentions: a condition whose satisfiability is asked of it. */
  private val limit = Declaration[BigInt]("a limit")
  private val underLimit = Node.claim("A number at the limit is positive.")(
    forall((limit: Term[BigInt]) => (limit === this.limit.term) implies positive(limit)))

  private val probed = FrModel("Probe")(everyIsSome, everyIsPositive, underLimit)

  /** A define making a booking with its start and end swapped, in a FrModel named as the record. */
  private val swapped = define { (r: Term[String], s: Term[BigInt], e: Term[BigInt]) => make[Booking](r, e, s) }
  private val startIsGiven = Node.claim("A swapped booking starts where it was asked to.")(
    forall((r: Term[String], s: Term[BigInt], e: Term[BigInt]) => swapped(r, s, e).start === s))
  private val namedAsRecord = FrModel("Booking")(startIsGiven)
  private val notNamedAsRecord = FrModel("Swaps")(startIsGiven)

  private def lean(kb: FrModel): String =
    Laid(Theories.resolved(kb), Map.empty, Nil).modules.map(Print.module).mkString("\n")
  private lazy val probe = lean(probed)

  test("a binder named some_ beside the Declaration some (Lean's some_) takes another name: no tautology") {
    assert(probe.contains("def claim (some_ : Int) : Prop :=\n  (∀ (some__ : Int), (some__ = some_))"), probe)
  }

  test("a binder named as the FrModel takes another name: a call of its define is not read as the binder's field") {
    assert(probe.contains("(∀ (Probe_1 : Int), (Probe.positive Probe_1))"), probe)
  }

  test("a formula printed in a whole-theory obligation takes the theory's names: satisfiable_ binds limit apart") {
    assert(probe.contains("∃ (limit : Int), (∃ (limit_1 : Int), (True ∧ (limit_1 = limit)))"), probe)
  }

  test("a FrModel named as a record is refused: its namespace would be the record's") {
    assert(Theories.problems(namedAsRecord).contains(Problem.DeclaredTwice("Booking")))
  }

  test("a field of a define's result stays a field: a swapped booking's start is not the start given") {
    val text = lean(notNamedAsRecord)
    assert(text.contains("((Swaps.swapped r s e).start = s)"), text)
  }
