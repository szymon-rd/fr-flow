package frflow.project.assumed

import frflow.core.analysis.Validate
import frflow.core.name.NodeId
import frflow.eval.assumed.{Lookup, Picking}
import frflow.project.{Live, Ported, Projects}
import frflow.proof.lean.print.Print
import scala.concurrent.duration.*

/** An operation known only by its assumptions (G2), in Lean: `has` is a constant of the register's state monad, a
  * program's step on it lifted by the class's `onState` (its field of the World, through `within`), a statement's run
  * of it `Register.has_run`; what is assumed of it is a hypothesis of every obligation of a program calling it, and it
  * is left open where consistency is asked (a witness written by hand, owner §39). A program relying on more than is
  * assumed stays unproven.
  */
class AssumedLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes
  private val elaborated = Projects.elaborated(Lookup.knowledge)
  private def spec(name: String): String = Projects.bare(elaborated).modules.find(_.name.dotted == name)
    .map(Print.module).getOrElse(fail(s"no $name"))
  private val whole = Ported.Lean(List("Whole" -> Ported.resource("assumed/Whole.lean")), Nil, None)

  test("valid: an operation known only by assumptions is a model's operation, its program's step") {
    assertEquals(Validate(elaborated).fold(_.toNonEmptyList.toList, _ => Nil), Nil)
  }

  test("in Lean: a constant of its model's state monad, lifted onto its field of the World by the class's onState") {
    val models = spec("FrFlowGen.Registers.Models")
    assert(models.contains("  onState : ∀ {α : Type}, StateM (List Int) α → m α") &&
      models.contains("  onState x := FrFlow.within (fun w => w.register) (fun w s => { w with register := s }) (x)") &&
      models.contains("def Register.has_run (has : Int → StateM (List Int) Prop) : Int → World → (Prop × World)"),
      models)
    val program = spec("FrFlowGen.Registers.Domain.Def_putOnceCode")
    assert(program.contains("(has : Int → StateM (List Int) Prop) : Int → m Unit") &&
      program.contains("let r ← Register.Ops.onState (has n)"), program)
  }

  test("what is assumed of it is a hypothesis of each obligation of a program calling it, and its run is read") {
    val impl = spec("FrFlowGen.Registers.putOnceStores.Spec")
    assert(impl.contains("∀ (has : Int → StateM (List Int) Prop), ∀ (h_hasAnswers : (Registers.hasAnswers.claim " +
      "has)) (h_hasKeeps : (Registers.hasKeeps.claim has)), (Registers.putOnceStores.claim " +
      "(Registers.putOnceCode_run has))"), impl)
    val cover = spec("FrFlowGen.Registers.noDuplicates.Spec")
    assert(cover.contains("def cover_putOnce : Prop :=\n  ∀ (has : Int → StateM (List Int) Prop), ∀ (h_hasAnswers"),
      cover)
    assert(spec("FrFlowGen.Registers.hasAnswers.Spec").contains("(match (Register.has_run has n world) with"))
    assert(spec("FrFlowGen.Registers.Whole.Spec").contains("∃ (has : Int → StateM (List Int) Prop), "))
  }

  test("Lean proves the program of what is assumed, and the whole consistent".tag(Live)) {
    Ported.run(elaborated, Nil, whole, Nil).map { r =>
      val rows = List("noDuplicates", "putOnceStores", "hasAnswers", "hasKeeps").map(n =>
        n -> Ported.row(r.analysis, NodeId(n)).take(3))
      assertEquals(rows, List("noDuplicates" -> List("claim", "proven", "proven"),
        "putOnceStores" -> List("claim", "proven", "proven"), "hasAnswers" -> List("assumption", "assumed", "proven"),
        "hasKeeps" -> List("assumption", "assumed", "proven")), Ported.table(r.analysis))
      assert(!Ported.unproven(r.analysis).values.flatten.exists(_.toString.contains("Consistency")),
        Ported.unproven(r.analysis))
    }
  }

  test("relying on more than is assumed (only a yes assumed right): the rule is not shown kept".tag(Live)) {
    Ported.run(Projects.elaborated(Lookup.halfAssumed), Nil, whole, Nil).map { r =>
      assertEquals(Ported.row(r.analysis, NodeId("noDuplicates")).take(3), List("claim", "open", "open"),
        Ported.table(r.analysis))
      assertEquals(Ported.row(r.analysis, NodeId("putOnceStores")).take(3), List("claim", "proven", "proven"),
        Ported.table(r.analysis))
    }
  }

  private val none = Ported.Lean(Nil, Nil, None)
  private def rows(kb: frflow.FrModel, ns: String*) = Ported.run(Projects.elaborated(kb), Nil, none, Nil).map(r =>
    ns.toList.map(n => n -> Ported.row(r.analysis, NodeId(n)).take(3)) -> Ported.table(r.analysis))

  test(("a claim about an operation known only by assumptions is proven from what is assumed of it, alone or as a " +
    "part: nothing says a picked number is positive, so neither it nor the claim it serves is (B3)").tag(Live)) {
    for
      (lone, t1) <- rows(Picking.lone, "pickedPositive")
      (part, t2) <- rows(Picking.AsPart.knowledge, "pickedPositive", "takenPositive")
    yield
      assertEquals(lone, List("pickedPositive" -> List("claim", "open", "open")), t1)
      assertEquals(part.head, "pickedPositive" -> List("claim", "open", "open"), t2)
      assertNotEquals(part(1)._2, List("claim", "proven", "proven"), t2)
  }

  test(("a claim about operations on a state alone is asked impl, where it was asked nothing and so stood proven: a " +
    "statement's run of an operation with steps is not read as its steps yet, so both stay open (fail closed)")
    .tag(Live)) {
    rows(Picking.puts, "putEmpties", "putHolds").map((rs, table) =>
      assertEquals(rs, List("putEmpties" -> List("claim", "open", "open"),
        "putHolds" -> List("claim", "open", "open")), table))
  }
