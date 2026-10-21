package frflow.check

import frflow.{Kernel, Project}
import frflow.ledger.*
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

/** Verifies nodes (the theory and each layer) against Lean and records results in the ledger.
  *
  * Per node:
  *   1. build the generated model and obligations. An error here is a model error:
  *      the Scala definitions translate to Lean that does not type-check;
  *   2. elaborate the generated `Auto` module, which tries `frflow_auto` on every
  *      obligation without an authored proof, and attribute failures to obligations;
  *   3. elaborate the authored proof file, if any, requiring every proof to state
  *      exactly `Obl.<name>` and rejecting constructs that weaken the environment;
  *   4. build the assembly, which feeds all proofs into the kernel theorems;
  *   5. audit the axioms of every resulting theorem.
  */
final class Checker(project: Project, runner: LeanRunner, allowedAxioms: Set[String] = Kernel.defaultAllowedAxioms):
  private val r = project.renderer

  def checkAll(only: Option[String] = None): Seq[NodeReport] =
    val ids = project.nodeIds.filter(id => only.forall(_ == id))
    ids.foldLeft(Vector.empty[NodeReport]) { (acc, id) =>
      val parent = project.parentNode(id)
      val parentReport = parent.flatMap(p => acc.find(_.nodeId == p)).orElse(parent.flatMap(previous))
      acc :+ checkNode(id, parentReport.map(_.verification))
    }

  private def previous(id: String): Option[NodeReport] =
    val ledger = Ledger.load(project.ws)
    val hashes = project.hashes
    ledger.entry(id).lastCheck.filter(c => hashes.get(id).exists(_.check == c.checkHash)).map { c =>
      NodeReport(id, c.verification, c.obligations, c.axioms, c.messages)
    }

  def checkNode(id: String, parentVerification: Option[Verification]): NodeReport =
    val obligations = r.obligations(id)

    // 1. model and obligations
    val model = runner.build(r.obligationsModule(id))
    if !model.ok then
      val diags = Diagnostics.parse(model.output).filter(_.isError)
      val msgs =
        if diags.isEmpty then Seq(model.output.linesIterator.toSeq.takeRight(20).mkString("\n"))
        else diags.map(d => s"${d.file}:${d.line}:${d.col}: ${d.message}")
      return NodeReport(id, Verification.ModelError,
        obligations.map(o => ObligationResult(o.name, ObligationStatus.Open, "model does not type-check")), Map.empty, msgs)

    // 2. automation
    val autoRel = r.autoPath(id)
    val autoResults = Files2.read(project.ws.lean(autoRel)).fold(Map.empty[String, ObligationResult]) { src =>
      val decls = ProofAuditor.declarations(src)
      val elab = runner.elaborate(autoRel)
      val errors = Diagnostics.parse(elab.output).filter(d => d.file.endsWith(autoRel) && d.isError)
      // Lean elaborates every theorem even when another fails; a failure without any
      // error in the file (a crash, a timeout) leaves every result unknown.
      val unknown = !elab.ok && errors.isEmpty
      decls.map { d =>
        val own = errors.filter(e => e.line >= d.startLine && e.line <= d.endLine)
        d.name -> (
          if unknown then ObligationResult(d.name, ObligationStatus.Open, "automation not checked: " + firstLine(elab.output))
          else if own.isEmpty then ObligationResult(d.name, ObligationStatus.Proven, "auto")
          else ObligationResult(d.name, ObligationStatus.Open, "automation failed: " + firstLine(own.head.message))
        )
      }.toMap
    }

    // 3. authored proofs
    val proofRel = r.proofsPath(id)
    val (authoredResults, fileMessages) = Files2.read(project.ws.lean(proofRel)) match
      case None      => (Map.empty[String, ObligationResult], Seq.empty[String])
      case Some(src) => checkProofs(id, proofRel, src)

    val results = obligations.map { o =>
      if r.isAuthored(id, o.name) then authoredResults.getOrElse(o.name, ObligationResult(o.name, ObligationStatus.Open, "missing"))
      else autoResults.getOrElse(o.name, ObligationResult(o.name, ObligationStatus.Open, "no automatic proof generated"))
    }

    val anyFailed = results.exists(_.status == ObligationStatus.Failed) || fileMessages.nonEmpty
    val anyOpen = results.exists(_.status == ObligationStatus.Open)
    if anyFailed then return NodeReport(id, Verification.Failed, results, Map.empty, fileMessages)
    if anyOpen then
      return NodeReport(id, Verification.Open, results, Map.empty,
        Seq(s"open obligations need an authored proof in lean/$proofRel (run `scaffold $id`)"))

    // 4. assembly
    if parentVerification.exists(_ != Verification.Proven) then
      return NodeReport(id, Verification.Discharged, results, Map.empty,
        Seq(s"all obligations discharged; assembly waits for parent ${project.parentNode(id).getOrElse("")} to be proven"))
    val assembly = runner.build(r.assemblyModule(id))
    if !assembly.ok then
      val diags = Diagnostics.parse(assembly.output).filter(_.isError)
      return NodeReport(id, Verification.Failed, results, Map.empty,
        "assembly failed: proofs do not compose into the kernel theorems" +:
          diags.map(d => s"${d.file}:${d.line}:${d.col}: ${d.message}"))

    // 5. axiom audit
    val audit = runner.elaborate(r.auditPath(id))
    val axioms = Diagnostics.parseAxioms(audit.output)
    val problems = r.auditedTheorems(id).flatMap { thm =>
      axioms.get(thm) match
        case None => Seq(s"axiom audit: no result for $thm")
        case Some(axs) =>
          val extra = axs -- allowedAxioms
          if extra.isEmpty then Nil else Seq(s"axiom audit: $thm depends on disallowed axioms ${extra.toSeq.sorted.mkString(", ")}")
    }
    val axiomMap = axioms.view.mapValues(_.toSeq.sorted).toMap
    if problems.nonEmpty || !audit.ok then
      val auditErrors = if audit.ok then Nil else Diagnostics.parse(audit.output).filter(_.isError).map(_.message)
      NodeReport(id, Verification.Failed, results, axiomMap, problems ++ auditErrors)
    else NodeReport(id, Verification.Proven, results, axiomMap, Nil)

  private def checkProofs(id: String, proofRel: String, src: String): (Map[String, ObligationResult], Seq[String]) =
    val decls = ProofAuditor.declarations(src)
    val violations = ProofAuditor.violations(src)
    val elab = runner.elaborate(proofRel)
    val diags = Diagnostics.parse(elab.output).filter(d => d.file.endsWith(proofRel))
    val errors = diags.filter(_.isError)
    val sorries = diags.filter(_.isSorry)
    val names = r.obligations(id).map(_.name).toSet

    def within(d: ProofAuditor.Decl)(line: Int) = line >= d.startLine && line <= d.endLine

    val results = decls.filter(d => names(d.name)).map { d =>
      val expectedStmt = s"Obl.${d.name}"
      val ownErrors = errors.filter(e => within(d)(e.line))
      val ownViolations = violations.filter(v => within(d)(v.line))
      val res =
        if d.statement != expectedStmt then
          ObligationResult(d.name, ObligationStatus.Failed, s"statement must be exactly `$expectedStmt`, found `${d.statement}`")
        else if ownViolations.nonEmpty then
          ObligationResult(d.name, ObligationStatus.Failed, s"forbidden: ${ownViolations.map(_.what).distinct.mkString(", ")}")
        else if ownErrors.nonEmpty then ObligationResult(d.name, ObligationStatus.Failed, firstLine(ownErrors.head.message))
        else if sorries.exists(s => within(d)(s.line)) then ObligationResult(d.name, ObligationStatus.Open, "uses sorry")
        else ObligationResult(d.name, ObligationStatus.Proven, "authored")
      d.name -> res
    }.toMap

    val obligationDecls = decls.filter(d => names(d.name))
    val outside = (line: Int) => !obligationDecls.exists(d => within(d)(line))
    val fileMessages =
      violations.filter(v => outside(v.line)).map(v => s"$proofRel:${v.line}: forbidden construct: ${v.what}") ++
        errors.filter(e => outside(e.line)).map(e => s"$proofRel:${e.line}:${e.col}: ${firstLine(e.message)}") ++
        sorries.filter(s => outside(s.line)).map(s => s"$proofRel:${s.line}: helper declaration uses sorry")
    (results, fileMessages)

  private def firstLine(s: String): String = s.linesIterator.map(_.trim).find(_.nonEmpty).getOrElse("").take(300)

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
