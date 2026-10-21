package frflow.examples.authz

import frflow.Project
import frflow.check.{Checker, LeanRunner}
import frflow.dsl.*
import frflow.ledger.{Approval, Ledger, ObligationStatus, Verification}
import frflow.model.*
import frflow.report.Reports
import frflow.workspace.{Files2, Workspace}
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/** End-to-end checks against Lean. Skipped when `lake` is not available. */
class AuthzIntegrationSuite extends munit.FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  private lazy val repoRoot: Path =
    Iterator.iterate(Paths.get(sys.props("user.dir")).toAbsolutePath)(_.getParent)
      .takeWhile(_ != null)
      .find(p => Files.exists(p.resolve("lean/FrFlow.lean")))
      .getOrElse(fail("repository root not found"))

  /** A fresh workspace containing the example's authored proofs. */
  private def workspace(): Workspace =
    val root = Files.createTempDirectory("frflow-authz")
    val src = repoRoot.resolve("examples/authz/lean/Proofs")
    Files.walk(src).iterator().asScala.filter(Files.isRegularFile(_)).foreach { f =>
      val target = root.resolve("lean/Proofs").resolve(src.relativize(f).toString)
      Files.createDirectories(target.getParent)
      Files.copy(f, target)
    }
    Workspace(root, repoRoot.resolve("lean").toString)

  private def check(theory: TheoryModel, ws: Workspace) =
    val project = Project(theory, ws)
    project.render()
    val runner = LeanRunner(ws.leanDir)
    assume(runner.available, "lake is not available")
    (project, Checker(project, runner).checkAndRecord())

  private def editProof(ws: Workspace, node: String)(f: String => String): Unit =
    val p = ws.lean(s"Proofs/Authz/$node.lean")
    Files2.writeIfChanged(p, f(Files2.read(p).get))

  private val theory = AuthzTheory.model

  test("the authorization theory is proven end to end") {
    val ws = workspace()
    val (project, reports) = check(theory, ws)
    assertEquals(reports.map(r => r.nodeId -> r.verification), Seq("T0" -> Verification.Proven, "T1" -> Verification.Proven))
    val t1 = reports.find(_.nodeId == "T1").get
    assert(t1.axioms.contains("Authz.T1.inherits_T0_Safe"), t1.axioms)
    assert(t1.axioms.values.flatten.forall(Set("propext", "Quot.sound", "Classical.choice")))
    assert(Reports.statusTable(project).contains("proven"))
  }

  test("an event that bypasses the policy cannot be proven to refine access") {
    // The kind of change an agent might add "for convenience": admins skip the policy decision.
    val bypass = event("adminAccess")
      .params("actor" -> "User", "t" -> "Token", "u" -> "User", "r" -> "Resource", "a" -> "Action")
      .assume(AssumptionRef("A1"), "∀ v, s.sessions p.t = some v → v = p.actor")
      .check("s.sessions p.t = some p.u")
      .act("{ s with log := ⟨p.u, p.r, p.a, s.version⟩ :: s.log }")
      .refines("access", witness = "{ u := p.actor, r := p.r, a := p.a }")
    val changed = theory.copy(nodes = theory.nodes.map { n =>
      if n.id == "T1" then n.copy(spec = n.spec.copy(events = n.spec.events :+ bypass)) else n
    })
    val ws = workspace()
    // The agent copies the proof of access_grd; it does not go through without the policy check.
    editProof(ws, "T1") { src =>
      src.replace(
        "end Authz.T1.Proofs",
        """theorem adminAccess_grd : Obl.adminAccess_grd := by
          |  intro s p _ g
          |  refine ⟨trivial, ?_⟩
          |  show s.policy s.version p.actor p.r p.a
          |  exact g.2.2
          |
          |end Authz.T1.Proofs""".stripMargin
      )
    }
    val (_, reports) = check(changed, ws)
    val t1 = reports.find(_.nodeId == "T1").get
    assertEquals(t1.verification, Verification.Failed)
    val grd = t1.obligations.find(_.name == "adminAccess_grd").get
    assertEquals(grd.status, ObligationStatus.Failed)
    assertEquals(t1.obligations.find(_.name == "adminAccess_sim").get.status, ObligationStatus.Open)
  }

  test("a proof of a weakened statement is rejected") {
    val ws = workspace()
    editProof(ws, "T1")(_.replace("theorem setPolicy_grd : Obl.setPolicy_grd := by\n  intro _ _ _ _\n  exact ⟨trivial, trivial⟩",
      "theorem setPolicy_grd : True := trivial"))
    val (_, reports) = check(theory, ws)
    val res = reports.find(_.nodeId == "T1").get.obligations.find(_.name == "setPolicy_grd").get
    assertEquals(res.status, ObligationStatus.Failed)
    assert(res.detail.contains("must be exactly"), res.detail)
  }

  test("sorry leaves the obligation open and the child waits for its parent") {
    val ws = workspace()
    editProof(ws, "T0")(_.replace("theorem init_Safe : Obl.init_Safe := by\n  intro s ⟨_, hlog⟩ e he\n  simp [hlog] at he",
      "theorem init_Safe : Obl.init_Safe := by\n  sorry"))
    val (_, reports) = check(theory, ws)
    val t0 = reports.find(_.nodeId == "T0").get
    assertEquals(t0.verification, Verification.Open)
    assertEquals(t0.obligations.find(_.name == "init_Safe").get.detail, "uses sorry")
    assertEquals(reports.find(_.nodeId == "T1").get.verification, Verification.Discharged)
  }

  test("changing a statement invalidates its approval but not the approvals of other nodes") {
    val ws = workspace()
    val project = Project(theory, ws)
    val hashes = project.hashes
    val ledger = Seq("T0", "T1").foldLeft(Ledger.empty)((l, id) =>
      l.updated(id)(_.copy(approval = Some(Approval(hashes(id).spec, "reviewer", "now"))))
    )
    Ledger.save(ws, ledger)
    val reworded = theory.copy(nodes = theory.nodes.map(n =>
      if n.id == "T1" then n.copy(statement = "Access is granted to the session principal under the current policy.") else n
    ))
    val statuses = Reports.statuses(Project(reworded, ws)).map(s => s.node.id -> s.approval).toMap
    assertEquals(statuses, Map("T0" -> "approved", "T1" -> "changed"))
  }
