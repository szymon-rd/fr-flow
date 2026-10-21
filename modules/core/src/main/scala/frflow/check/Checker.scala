package frflow.check

import frflow.{Kernel, Project}
import frflow.ledger.*
import frflow.model.Node
import frflow.workspace.Files2
import java.time.Instant

final case class NodeReport(
    nodeId: String,
    verification: Verification,
    obligations: Seq[ObligationResult],
    axioms: Map[String, Seq[String]],
    messages: Seq[String]
):
  def proven: Int = obligations.count(_.status == ObligationStatus.Proven)

/** Verifies nodes against Lean and records results in the ledger.
  *
  * Per node:
  *   1. build the generated model and obligations (an error here is a model error:
  *      the theory's Lean fragments do not type-check);
  *   2. elaborate the authored proof file and attribute diagnostics to obligations,
  *      requiring every proof to state exactly `Obl.<name>`;
  *   3. build the assembly, which feeds the proofs into the kernel theorems
  *      (`Machine.refinement` / `Machine.invariant`);
  *   4. audit the axioms of every resulting theorem.
  */
final class Checker(project: Project, runner: LeanRunner, allowedAxioms: Set[String] = Kernel.defaultAllowedAxioms):
  private val r = project.renderer
  private val theory = project.theory

  def checkAll(only: Option[String] = None): Seq[NodeReport] =
    val nodes = theory.topological.filter(n => only.forall(_ == n.id))
    nodes.foldLeft(Vector.empty[NodeReport]) { (acc, n) =>
      val parentReport = n.parent.flatMap(p => acc.find(_.nodeId == p)).orElse(n.parent.flatMap(previous))
      acc :+ checkNode(n, parentReport.map(_.verification))
    }

  private def previous(id: String): Option[NodeReport] =
    val ledger = Ledger.load(project.ws)
    val hashes = project.hashes
    ledger.entry(id).lastCheck.filter(c => hashes.get(id).exists(_.check == c.checkHash)).map { c =>
      NodeReport(id, c.verification, c.obligations, c.axioms, c.messages)
    }

  def checkNode(n: Node, parentVerification: Option[Verification]): NodeReport =
    val obligations = r.obligations(n)

    // 1. model and obligations
    val model = runner.build(r.obligationsModule(n))
    if !model.ok then
      val diags = Diagnostics.parse(model.output).filter(_.isError)
      val msgs =
        if diags.isEmpty then Seq(model.output.linesIterator.toSeq.takeRight(20).mkString("\n"))
        else diags.map(d => s"${d.file}:${d.line}:${d.col}: ${d.message}")
      return NodeReport(n.id, Verification.ModelError, obligations.map(o => ObligationResult(o.name, ObligationStatus.Open, "model does not type-check")), Map.empty, msgs)

    // 2. proofs
    val proofRel = r.proofsPath(n)
    val source = Files2.read(project.ws.lean(proofRel))
    val (results, fileMessages) = source match
      case None =>
        (obligations.map(o => ObligationResult(o.name, ObligationStatus.Open, "no proof file (run scaffold)")), Seq.empty[String])
      case Some(src) => checkProofs(n, proofRel, src)

    val anyFailed = results.exists(_.status == ObligationStatus.Failed) || fileMessages.nonEmpty
    val anyOpen = results.exists(_.status == ObligationStatus.Open)
    if anyFailed then return NodeReport(n.id, Verification.Failed, results, Map.empty, fileMessages)
    if anyOpen then return NodeReport(n.id, Verification.Open, results, Map.empty, Nil)

    // 3. assembly
    if parentVerification.exists(_ != Verification.Proven) then
      return NodeReport(
        n.id, Verification.Discharged, results, Map.empty,
        Seq(s"all obligations discharged; assembly waits for parent ${n.parent.getOrElse("")} to be proven")
      )
    val assembly = runner.build(r.assemblyModule(n))
    if !assembly.ok then
      val diags = Diagnostics.parse(assembly.output).filter(_.isError)
      return NodeReport(
        n.id, Verification.Failed, results, Map.empty,
        "assembly failed: proofs do not compose into the kernel theorems" +:
          diags.map(d => s"${d.file}:${d.line}:${d.col}: ${d.message}")
      )

    // 4. axiom audit
    val audit = runner.elaborate(r.auditPath(n))
    val axioms = Diagnostics.parseAxioms(audit.output)
    val expected = r.auditedTheorems(n)
    val problems = expected.flatMap { thm =>
      axioms.get(thm) match
        case None => Seq(s"axiom audit: no result for $thm")
        case Some(axs) =>
          val extra = axs -- allowedAxioms
          if extra.isEmpty then Nil else Seq(s"axiom audit: $thm depends on disallowed axioms ${extra.toSeq.sorted.mkString(", ")}")
    }
    val axiomMap = axioms.view.mapValues(_.toSeq.sorted).toMap
    if problems.nonEmpty || !audit.ok then
      val auditErrors = if audit.ok then Nil else Diagnostics.parse(audit.output).filter(_.isError).map(_.message)
      NodeReport(n.id, Verification.Failed, results, axiomMap, problems ++ auditErrors)
    else NodeReport(n.id, Verification.Proven, results, axiomMap, Nil)

  private def checkProofs(n: Node, proofRel: String, src: String): (Seq[ObligationResult], Seq[String]) =
    val decls = ProofAuditor.declarations(src)
    val violations = ProofAuditor.violations(src)
    val elab = runner.elaborate(proofRel)
    val diags = Diagnostics.parse(elab.output).filter(d => d.file.endsWith(proofRel))
    val errors = diags.filter(_.isError)
    val sorries = diags.filter(_.isSorry)

    def within(d: ProofAuditor.Decl)(line: Int) = line >= d.startLine && line <= d.endLine

    val results = r.obligations(n).map { o =>
      decls.find(_.name == o.name) match
        case None => ObligationResult(o.name, ObligationStatus.Open, "missing")
        case Some(d) =>
          val expectedStmt = s"Obl.${o.name}"
          val ownErrors = errors.filter(e => within(d)(e.line))
          val ownViolations = violations.filter(v => within(d)(v.line))
          if d.statement != expectedStmt then
            ObligationResult(o.name, ObligationStatus.Failed, s"statement must be exactly `$expectedStmt`, found `${d.statement}`")
          else if ownViolations.nonEmpty then
            ObligationResult(o.name, ObligationStatus.Failed, s"forbidden: ${ownViolations.map(_.what).distinct.mkString(", ")}")
          else if ownErrors.nonEmpty then
            ObligationResult(o.name, ObligationStatus.Failed, firstLine(ownErrors.head.message))
          else if sorries.exists(s => within(d)(s.line)) then
            ObligationResult(o.name, ObligationStatus.Open, "uses sorry")
          else ObligationResult(o.name, ObligationStatus.Proven)
    }

    val obligationDecls = decls.filter(d => r.obligations(n).exists(_.name == d.name))
    val outside = (line: Int) => !obligationDecls.exists(d => within(d)(line))
    val fileMessages =
      violations.filter(v => outside(v.line)).map(v => s"$proofRel:${v.line}: forbidden construct: ${v.what}") ++
        errors.filter(e => outside(e.line)).map(e => s"$proofRel:${e.line}:${e.col}: ${firstLine(e.message)}") ++
        sorries.filter(s => outside(s.line)).map(s => s"$proofRel:${s.line}: helper declaration uses sorry")
    (results, fileMessages)

  private def firstLine(s: String): String = s.linesIterator.nextOption().getOrElse("").take(300)

  /** Runs the checks and writes the results into the ledger. */
  def checkAndRecord(only: Option[String] = None): Seq[NodeReport] =
    val reports = checkAll(only)
    val hashes = project.hashes
    val now = Instant.now().toString
    val ledger = reports.foldLeft(Ledger.load(project.ws)) { (l, rep) =>
      l.updated(rep.nodeId)(e =>
        e.copy(lastCheck = Some(CheckRecord(hashes(rep.nodeId).check, rep.verification, rep.obligations, rep.axioms, rep.messages, now)))
      )
    }
    Ledger.save(project.ws, ledger)
    reports
