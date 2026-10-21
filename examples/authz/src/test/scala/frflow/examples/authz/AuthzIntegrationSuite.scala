package frflow.examples.authz

import frflow.Project
import frflow.check.{Checker, LeanRunner, NodeReport}
import frflow.dsl.*
import frflow.examples.authz.domain.*
import frflow.ledger.{Approval, Ledger, ObligationStatus, Verification}
import frflow.model.{TargetModel, TheoryModel}
import frflow.report.Reports
import frflow.workspace.{Files2, Workspace}
import java.nio.file.{Files, Path, Paths}

/** An implementation step an agent might add "for convenience": administrators skip the policy decision. */
object Shortcut
    extends Implementation[ServiceState, SessionState](D1, "Shortcut", "AdminShortcut",
      statement = "Administrators are always allowed.", rationale = "Test fixture."):
  abstraction(s => SessionState(s.version, v => (u, r, a) => s.permittedAt(v, u, r, a), s.sessions, s.log))
  initial(ServiceState(0, Map.empty, Map.empty, Nil))
  val adminAccess = operation[Request]("adminAccess", "Administrators skip the policy decision.")
    .check((s, r) => s.sessions.get(r.token).exists(u => u.name == "admin"))
    .act((s, r) => s.copy(log = Access(s.principal(r.token), r.resource, r.action, s.version) :: s.log))
    .refines(D1.access)((_, r) => r)

/** A theory with a law that automation does not prove (nonlinear arithmetic). */
object SquareTheory extends Theory("Square"):
  law("SquareNonNegative", "A square is never negative.")((n: Int) => n * n >= 0)

/** End-to-end checks against Lean. Skipped when `lake` is not available. */
class AuthzIntegrationSuite extends munit.FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  private lazy val repoRoot: Path =
    Iterator.iterate(Paths.get(sys.props("user.dir")).toAbsolutePath)(_.getParent)
      .takeWhile(_ != null)
      .find(p => Files.exists(p.resolve("lean/FrFlow.lean")))
      .getOrElse(fail("repository root not found"))

  private def workspace(): Workspace =
    Workspace(Files.createTempDirectory("frflow-it"), repoRoot.resolve("lean").toString)

  private def check(project: Project, only: Option[String] = None): Seq[NodeReport] =
    project.render()
    val runner = LeanRunner(project.ws.leanDir)
    assume(runner.available, "lake is not available")
    Checker(project, runner).checkAndRecord(only)

  private val model = TheoryModel.from(AuthzModel)

  test("the model is proven end to end, by automation alone") {
    val project = Project(model, workspace())
    val reports = check(project)
    assertEquals(reports.map(r => r.nodeId -> r.verification),
      Seq("Theory" -> Verification.Proven, "R0" -> Verification.Proven, "D1" -> Verification.Proven, "I2" -> Verification.Proven))
    assert(reports.flatMap(_.obligations).forall(_.detail == "auto"))
    val i2 = reports.find(_.nodeId == "I2").get
    assert(i2.axioms.contains("Authz.I2.inherits_R0_Safe"), i2.axioms)
    assert(i2.axioms.values.flatten.forall(Set("propext", "Quot.sound", "Classical.choice")))
    assert(!Files.exists(project.ws.lean("Proofs")), "no proof was written by hand")
  }

  test("an operation that bypasses the policy cannot be proven to refine access") {
    val bypass = TheoryModel.from(Model(AuthzTheory, R0, D1, Shortcut)).layerOrFail("Shortcut").ops.head
    assertEquals(bypass.target match { case TargetModel.Refines(l, o, _) => s"$l.$o"; case other => other.toString }, "D1.access")
    val changed = model.copy(layers = model.layers.map(l => if l.id == "I2" then l.copy(ops = l.ops :+ bypass) else l))
    val ws = workspace()
    val project = Project(changed, ws)
    val i2 = check(project).find(_.nodeId == "I2").get
    assertEquals(i2.verification, Verification.Open)
    val grd = i2.obligations.find(_.name == "adminAccess_grd").get
    assertEquals(grd.status, ObligationStatus.Open)
    assert(grd.detail.startsWith("automation failed"), grd.detail)
    assert(i2.obligations.filter(_.name != "adminAccess_grd").forall(_.status == ObligationStatus.Proven))

    // An agent cannot make it pass by proving something weaker.
    project.scaffold("I2", Seq("adminAccess_grd"))
    val proofs = ws.lean("Proofs/Authz/I2.lean")
    Files2.writeIfChanged(proofs, Files2.read(proofs).get.replace(
      "theorem adminAccess_grd : Obl.adminAccess_grd := by\n  unfold Obl.adminAccess_grd\n  sorry",
      "theorem adminAccess_grd : True := trivial"))
    val again = check(project, Some("I2")).head
    assertEquals(again.verification, Verification.Failed)
    assert(again.obligations.find(_.name == "adminAccess_grd").get.detail.contains("must be exactly `Obl.adminAccess_grd`"))
  }

  test("an obligation automation cannot prove is proven in an authored file, kept apart from the model") {
    val ws = workspace()
    val project = Project(Model(SquareTheory), ws)
    val first = check(project).head
    assertEquals(first.verification, Verification.Open)
    assert(first.obligations.head.detail.contains("frflow_auto found no proof"), first.obligations.head.detail)

    assertEquals(project.scaffold("Theory", Seq("SquareNonNegative")), Seq("SquareNonNegative"))
    val stub = check(project).head
    assertEquals(stub.obligations.head.detail, "uses sorry")
    assert(!Files2.read(ws.lean("FrFlowGen/Square/Theory/Auto.lean")).get.contains("theorem SquareNonNegative"),
      "an authored obligation is not attempted automatically")

    val proofs = ws.lean("Proofs/Square/Theory.lean")
    Files2.writeIfChanged(proofs, Files2.read(proofs).get.replace(
      "  unfold Obl.SquareNonNegative\n  sorry",
      """  unfold Obl.SquareNonNegative
        |  intro n
        |  rcases Int.le_total 0 n with h | h
        |  · exact Int.mul_nonneg h h
        |  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
        |    simpa [Int.neg_mul_neg] using this""".stripMargin))
    val done = check(project).head
    assertEquals(done.verification, Verification.Proven)
    assertEquals(done.obligations.head.detail, "authored")
    assert(done.axioms.contains("Square.Laws.SquareNonNegative"), done.axioms)
  }

  test("a changed statement invalidates only that layer's approval") {
    val ws = workspace()
    val project = Project(model, ws)
    val approved = project.nodeIds.foldLeft(Ledger.load(ws)) { (l, id) =>
      l.updated(id)(_.copy(approval = Some(Approval(project.hashes(id).spec, "reviewer", "now"))))
    }
    Ledger.save(ws, approved)
    assert(Reports.statuses(project).forall(_.approval == "approved"))

    val reworded = model.copy(layers = model.layers.map(l =>
      if l.id == "D1" then l.copy(statement = "Access is granted to the session principal under the current policy.") else l))
    val after = Reports.statuses(Project(reworded, ws)).map(s => s.id -> s.approval).toMap
    assertEquals(after, Map("Theory" -> "approved", "R0" -> "approved", "D1" -> "changed", "I2" -> "approved"))
  }
