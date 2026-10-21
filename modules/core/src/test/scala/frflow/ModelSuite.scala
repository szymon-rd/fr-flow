package frflow

import frflow.dsl.LayerKind
import frflow.fixtures.*
import frflow.ir.*
import frflow.lint.{Lints, Severity}
import frflow.model.*
import frflow.obligation.Obligations
import frflow.render.LeanRenderer
import frflow.runtime.{Outcome, Service}

/** Snapshot, obligations, Lean rendering, lints and the runtime, on the counter fixture. */
class ModelSuite extends munit.FunSuite:

  private val m = TheoryModel.from(CounterModel)
  private val r = LeanRenderer(m)
  private val c0 = m.layerOrFail("C0")
  private val c1 = m.layerOrFail("C1")

  test("the snapshot records layers, kinds, links and the domain") {
    assertEquals(m.layers.map(l => l.id -> l.kind), List("C0" -> LayerKind.Requirements, "C1" -> LayerKind.Implementation))
    assertEquals(c1.parent, Some("C0"))
    assertEquals(c1.cites, List("E1"))
    assertEquals(m.domain, List(Type.Named("Mode"), Type.Named("Register")))
    assert(c1.link.flatMap(_.glue).isDefined)
    assert(m.theoryDefs.contains("Register.canInc"), m.theoryDefs)
    assertEquals(m.layerDefs(c0), List("Bounded", "Limits.Max"))
  }

  test("obligations of the requirements and implementation layers") {
    assertEquals(Obligations.forLayer(m, c0).map(_.name), List("init_LeMax", "inc_inv_LeMax", "reset_inv_LeMax"))
    assertEquals(
      Obligations.forLayer(m, c1).map(_.name),
      List("init_glue", "init_abs", "inc_inv_glue", "inc_grd", "inc_sim", "reset_inv_glue", "reset_grd", "reset_sim",
        "freeze_inv_glue", "freeze_skip")
    )
    val grd = Obligations.forLayer(m, c1).find(_.name == "inc_grd").get
    assertEquals(grd.statement, "∀ s p, Obl.Hyp s → inc.guard s p → C0.inc.guard (abs s) (inc.witness s p)")
    assertEquals(Obligations.forTheory(m).map(o => o.name -> o.statement), List("MaxPositive" -> "Limits.Max > 0"))
  }

  test("the model of a layer is rendered from the Scala definitions") {
    val model = r.renderModel(c1)
    assert(model.contains("abbrev State := Register"), model)
    assert(model.contains("def Init (s : State) : Prop := s = (Register.mk 0 Limits.Max Mode.Counting)"), model)
    assert(model.contains("def inc.assume (s : State) (p : Unit) : Prop := s.cap > 0"), model)
    assert(model.contains("def inc.check (s : State) (p : Unit) : Prop := Register.canInc s"), model)
    assert(model.contains("def inc.act (s : State) (p : Unit) : State := { s with n := s.n + 1 }"), model)
    assert(model.contains("def abs (s : State) : C0.State := Bounded.mk s.n"), model)
    assert(model.contains("def glue (s : State) : Prop := s.cap ≤ Limits.Max"), model)
    assert(model.contains("def inc.witness (s : State) (p : Unit) : Unit := ()"), model)
    assert(model.contains("def machine : FrFlow.Machine := ⟨State, Init, [inc.event, reset.event, freeze.event]⟩"), model)
  }

  test("the domain is rendered in dependency order") {
    val d = r.renderDomain
    assert(d.indexOf("inductive Mode where") < d.indexOf("structure Register where"), d)
    assert(d.indexOf("def Limits.Max") < d.indexOf("def Register.canInc"), d)
    assert(d.contains("  /-- configured maximum -/\n  cap : Int"), d)
    assert(d.contains("(s.mode = Mode.Counting) ∧ (s.n < s.cap)") || d.contains("(self.mode = Mode.Counting) ∧ (self.n < self.cap)"), d)
  }

  test("automation covers every obligation without an authored proof") {
    val auto = r.renderAuto("C1")
    assertEquals("theorem ".r.findAllIn(auto).size, 10)
    assert(auto.contains("theorem inc_grd : Obl.inc_grd := by\n  unfold Obl.inc_grd\n  frflow_auto"), auto)
    val withAuthored = LeanRenderer(m, Map("C1" -> Set("inc_grd")))
    assert(!withAuthored.renderAuto("C1").contains("inc_grd"))
    val asm = withAuthored.renderAssembly(c1)
    assert(asm.contains("import Proofs.Counter.C1"), asm)
    assert(asm.contains("Counter.C1.Proofs.inc_grd Counter.C1.Auto.inc_sim"), asm)
  }

  test("assembly builds the refinement and inherits the requirement") {
    val asm = r.renderAssembly(c1)
    assert(asm.contains("EventSim.refines C0.inc.event (List.Mem.head _) inc.witness"), asm)
    assert(asm.contains("EventSim.refines C0.reset.event (List.Mem.tail _ (List.Mem.head _)) reset.witness"), asm)
    assert(asm.contains("EventSim.skip (fun s p h g => Counter.C1.Auto.freeze_inv_glue s p h g) Counter.C1.Auto.freeze_skip"), asm)
    assert(asm.contains("theorem inherits_C0_LeMax : Invariant machine.toSpec (fun s => C0.LeMax (C1.abs (s)))"), asm)
    assertEquals(r.auditedTheorems("C1"), List("Counter.C1.refinement", "Counter.C1.inherits_C0_LeMax"))
    assertEquals(r.auditedTheorems("Theory"), List("Counter.Laws.MaxPositive"))
  }

  test("the fixture has no lint errors") {
    val issues = Lints.run(m)
    assertEquals(Lints.errors(issues), Nil)
  }

  private def codes(mm: TheoryModel): Set[String] = Lints.errors(Lints.run(mm)).map(_.code).toSet

  private def withLayer(id: String)(f: LayerModel => LayerModel): TheoryModel =
    m.copy(layers = m.layers.map(l => if l.id == id then f(l) else l))

  test("an implementation must be the last refinement") {
    val child = c1.copy(id = "C2", parent = Some("C1"))
    assert(codes(m.copy(layers = m.layers :+ child))("FR026"))
  }

  test("operations of a refining layer must refine a parent operation, of the parent") {
    val unspecified = withLayer("C1")(l => l.copy(ops = l.ops.map(o => if o.name == "freeze" then o.copy(target = TargetModel.Unspecified) else o)))
    assert(codes(unspecified)("FR045"))
    val wrongLayer = withLayer("C1")(l => l.copy(ops = l.ops.map {
      case o @ OpModel(_, _, _, _, _, _, TargetModel.Refines(_, op, w)) => o.copy(target = TargetModel.Refines("X9", op, w))
      case o => o
    }))
    assert(codes(wrongLayer)("FR046"))
    val rootRefines = withLayer("C0")(l => l.copy(ops = l.ops.map(o => o.copy(target = TargetModel.Skip))))
    assert(codes(rootRefines)("FR044"))
  }

  test("the implementation must be executable") {
    val quant = Expr.Quant(Quantifier.All, List(Param("x", Type.Int)), Expr.BoolLit(true))
    val withQuant = withLayer("C1")(l => l.copy(ops = l.ops.map(o => o.copy(checks = o.checks.map(c => c.copy(body = quant))))))
    assert(codes(withQuant)("FR042"))
    val fnState = m.copy(defs = m.defs.copy(adts = m.defs.adts.updated("Register",
      m.defs.adts("Register").copy(shape = AdtShape.Product(List(FieldDef("f", Type.Fun(List(Type.Int), Type.Bool), "")))))))
    assert(codes(fnState)("FR040"))
  }

  test("statements are bounded and names are not reserved") {
    assert(codes(withLayer("C0")(_.copy(statement = "x" * 401)))("FR022"))
    assert(codes(withLayer("C0")(_.copy(statement = "One. Two. Three. Four.")))("FR023"))
    val reserved = m.copy(defs = m.defs.copy(adts = m.defs.adts.updated("Mode", m.defs.adts("Mode").copy(name = "State"))))
    assert(codes(reserved)("FR015"))
    assert(codes(withLayer("C1")(_.copy(link = None)))("FR027"))
  }

  test("assumptions nobody cites are reported") {
    val uncited = withLayer("C1")(l => l.copy(cites = Nil, ops = l.ops.map(_.copy(assumes = Nil))))
    assert(Lints.run(uncited).exists(i => i.code == "FR011" && i.severity == Severity.Warning))
  }

  test("the runtime executes the implementation's Scala code") {
    val svc = Service(C1)
    assertEquals(svc.state, Register(0, 10, Mode.Counting))
    (1 to 10).foreach(_ => assert(svc.submit(C1.inc, ()).accepted))
    assertEquals(svc.submit(C1.inc, ()), Outcome.Rejected("inc"))
    assertEquals(svc.state.n, 10)
    svc.submit(C1.reset, ())
    svc.submit(C1.freeze, ())
    assertEquals(svc.submit(C1.inc, ()), Outcome.Rejected("inc"))
    assertEquals(Service.step(C1.inc, Register(0, 1, Mode.Counting), ()), Outcome.Accepted(Register(1, 1, Mode.Counting)))
  }

  test("operations of another layer are refused by a service") {
    val svc = Service(C1)
    intercept[IllegalArgumentException](svc.submit(C0.inc.asInstanceOf[frflow.dsl.Operation[Register, Unit]], ()))
  }
