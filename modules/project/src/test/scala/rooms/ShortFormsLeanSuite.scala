package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.dsl.build.Fault
import frflow.project.{Live, Ported, Projects}
import frflow.proof.lean.print.Print
import scala.concurrent.duration.*

/** The short forms as Lean is given them: `exists` is `∃`, what always holds of its variable a conjunct below it;
  * an option's operations are the folds an author would write; a run's `ifSucceeds` and `ifFails` are its result's
  * fold, true on the other side. Each is printed as written.
  */
class ShortFormsLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 30.minutes

  private val nine = Node.claim("Some booking starts at nine.")(
    exists((b: Term[Booking]) => b.start === 9)).assuming(bookingsEndAfterStart)
  private val pair = Node.claim("Two bookings of one room start apart.")(
    exists((a: Term[Booking], b: Term[Booking]) => a.room === b.room && a.start < b.start))
    .assuming(bookingsEndAfterStart)
  private val kb = FrModel("Rooms")(nine, pair, bookingsEndAfterStart)

  private def spec(kb: FrModel, id: String): String = Projects.bare(Projects.elaborated(kb)).modules
    .find(_.name.dotted == s"FrFlowGen.Rooms.$id.Spec").map(Print.module).getOrElse(fail(s"no $id"))
  private def claim(kb: FrModel, id: String): String =
    spec(kb, id).linesIterator.dropWhile(!_.contains("def claim")).take(2).mkString("\n")

  test("exists is Lean's ∃, what always holds of its variable a conjunct below it, as it is a premise of forall") {
    val one = claim(kb, "nine")
    assert(one.contains("∃ (b : Booking), ((Rooms.bookingsEndAfterStart b) ∧ ("), one)
    val two = claim(kb, "pair")
    assert(two.contains("∃ (a : Booking), ((Rooms.bookingsEndAfterStart a) ∧ (∃ (b : Booking), " +
      "((Rooms.bookingsEndAfterStart b) ∧ "), two)
  }

  test("exists is shown as written") {
    val said = Projects.elaborated(kb).theory.nodes.map(_.node).find(_.id == NodeId("nine"))
      .flatMap(_.statement.said)
    assertEquals(said.map(_.source.value), Some("exists((b: Term[Booking]) => b.start === 9)"))
  }

  test("isConstant under an exists is refused: no step keeps it there") {
    val opening = Declaration[BigInt]("the hour the rooms open")
    val under = Node.claim("Some hour stays the opening hour.")(
      exists((h: Term[BigInt]) => h === opening && opening.isConstant))
    val faults = FrModel("Rooms")(under).elaborated.fold(_.toNonEmptyList.toList.map(_.fault), _ => Nil)
    assertEquals(faults, List(Fault.ConstantInside("inside a value")))
  }

  test("an option's operations are the folds an author writes: the same Lean") {
    val held = define { (o: Term[Option[Booking]]) => o.map(b => b.start).contains(9) }
    val folded = define { (o: Term[Option[Booking]]) =>
      o.fold(none[BigInt])(b => some(b.start)).fold(False)(a => a === 9) }
    def body(kb: FrModel, d: String) = Projects.bare(Projects.elaborated(kb)).modules
      .find(_.name.dotted == s"FrFlowGen.Rooms.Domain.Def_$d").map(Print.module).getOrElse(fail(s"no $d"))
      .linesIterator.dropWhile(!_.contains(s"def $d")).mkString("\n").replace(d, "d")
    val sugar = FrModel("Rooms")(Node.claim("Holds.")(forall((o: Term[Option[Booking]]) => held(o) === held(o))))
    val plain = FrModel("Rooms")(Node.claim("Holds.")(forall((o: Term[Option[Booking]]) => folded(o) === folded(o))))
    assertEquals(body(sugar, "held"), body(plain, "folded"))
    assert(body(sugar, "held").contains("match"), body(sugar, "held"))
  }

  test("Lean proves an exists claim from its part, given the witness".tag(Live)) {
    val above = Declaration[BigInt => Boolean]("whether a number is above the limit")
    val some = Node.claim("Some number is above the limit.")(exists((n: Term[BigInt]) => above(n)))
    val which = Node.claim("A number is above the limit exactly when it is over three.")(
      forall((n: Term[BigInt]) => above(n) === (3 < n))).refines(some)
    val proof = """import FrFlowGen.Limits.some.Spec
      |
      |set_option autoImplicit false
      |noncomputable section
      |open Classical
      |
      |namespace Limits.some.Proofs
      |
      |theorem complete : Obl.complete := by
      |  intro above h
      |  exact ⟨4, by rw [h]; decide⟩
      |
      |end Limits.some.Proofs
      |""".stripMargin
    Ported.run(Projects.elaborated(FrModel("Limits")(some, which)), Nil,
      Ported.Lean(List("some" -> proof), Nil, None), Nil).map { r =>
      assertEquals(Ported.row(r.analysis, NodeId("some")).take(3), List("claim", "proven", "proven"),
        Ported.table(r.analysis))
    }
  }
