package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.dsl.build.Fault
import frflow.project.{Live, Ported, Projects}
import frflow.proof.lean.print.Print
import scala.concurrent.duration.*

/** A define over Declarations (`stated`), used only in statements: a define in Lean like any other, the Declarations
  * it applies its inputs before its own; taking the world last where one of them changes with the World. Code cannot
  * call it: it does not compile, as a Declaration named in code does not.
  */
class StatedLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 30.minutes

  val above = Declaration[BigInt => Boolean]("whether a number is above the limit")
  val aboveThree = stated { (n: Term[BigInt]) => above(n) === (3 < n) }
  val someAbove = Node.claim("Some number is above the limit.")(exists((n: Term[BigInt]) => above(n)))
  val which = Node.claim("A number is above the limit exactly when it is over three.")(
    forall((n: Term[BigInt]) => aboveThree(n))).refines(someAbove)

  val opening = Declaration[BigInt]("the hour the rooms open")
  val opensBy = stated { (hour: Term[BigInt]) => opening <= hour }
  val bookedOpen = Node.claim("Every booking held starts once the rooms are open.")(
    storedBookings.current.forall(b => opensBy(b.start)))

  private def module(kb: FrModel, name: String): String = Projects.bare(Projects.elaborated(kb)).modules
    .find(_.name.dotted == s"FrFlowGen.${kb.name.value}.$name").map(Print.module).getOrElse(fail(s"no $name"))

  test("a stated define is a define in Lean, taking the Declarations it applies first, and a statement calls it") {
    val kb = FrModel("Limits")(someAbove, which)
    assert(module(kb, "Domain.Def_aboveThree").contains(
      "def aboveThree (above : Int → Prop) (n : Int) : Prop :=\n  ((above n) = ((3 : Int) < n))"),
      module(kb, "Domain.Def_aboveThree"))
    assert(module(kb, "which.Spec").contains("(∀ (n : Int), (Limits.aboveThree above n))"), module(kb, "which.Spec"))
  }

  test("a Declaration changing with the World, applied in a stated define, is read in the world the define takes") {
    val kb = FrModel("Rooms")(bookedOpen)
    val define = module(kb, "Domain.Def_opensBy")
    assert(define.contains("def opensBy (opening : World → Int) (hour : Int) (world : World) : Prop :="), define)
    assert(define.contains("((opening world) ≤ hour)"), define)
    assert(module(kb, "bookedOpen.Spec").contains("(Rooms.opensBy opening b.start world)"),
      module(kb, "bookedOpen.Spec"))
  }

  test("a rule calling a stated define over a Declaration changing with the World is refused, as one applying it") {
    val rule = Node.claim("Every booking starts once the rooms are open.")(always[Booking](b => opensBy(b.start)))
    val faults = FrModel("Rooms")(bookedOpen, rule).elaborated.fold(_.toNonEmptyList.toList.map(_.fault), _ => Nil)
    assertEquals(faults, List(Fault.RuleOverChanging("opening", "rule", "bookedOpen")))
  }

  test("code cannot call a stated define: a program, a define and plain code calling one do not compile") {
    val message = "said only in a statement"
    assert(compileErrors("program { (n: Term[BigInt]) => Flow.pure(aboveThree(n)) }").contains(message))
    assert(compileErrors("define { (n: Term[BigInt]) => aboveThree(n) }").contains(message))
    assert(compileErrors("Declaration[BigInt => Boolean](\"x\").define(aboveThree)").nonEmpty)
  }

  test("Lean proves an exists claim from a part stated with a stated define, and the part feasible".tag(Live)) {
    val proof = """import FrFlowGen.Limits.someAbove.Spec
      |
      |set_option autoImplicit false
      |noncomputable section
      |open Classical
      |
      |namespace Limits.someAbove.Proofs
      |
      |theorem complete : Obl.complete := by
      |  intro above h
      |  have h4 : Limits.aboveThree above 4 := h 4
      |  unfold Limits.aboveThree at h4
      |  exact ⟨4, by rw [h4]; decide⟩
      |
      |theorem feasible : Obl.feasible := by
      |  refine ⟨fun n => 3 < n, fun n => rfl⟩
      |
      |end Limits.someAbove.Proofs
      |""".stripMargin
    Ported.run(Projects.elaborated(FrModel("Limits")(someAbove, which)), Nil,
      Ported.Lean(List("someAbove" -> proof), Nil, None), Nil).map { r =>
      assertEquals(List("someAbove", "which").map(n => Ported.row(r.analysis, NodeId(n)).take(3)),
        List(List("claim", "proven", "proven"), List("claim", "proven", "proven")), Ported.table(r.analysis))
    }
  }
