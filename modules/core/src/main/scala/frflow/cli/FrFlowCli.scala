package frflow.cli

import frflow.Project
import frflow.check.{Checker, LeanRunner, NodeReport}
import frflow.dsl.TheoryDef
import frflow.ledger.{Approval, Ledger, ObligationStatus}
import frflow.lint.{Lints, Severity}
import frflow.report.Reports
import frflow.workspace.{Files2, Workspace}
import java.nio.file.Paths
import java.time.Instant

/** Command-line entry point. A theory project exposes it with:
  * {{{
  * @main def authz(args: String*): Unit =
  *   sys.exit(FrFlowCli.run(AuthzTheory, Workspace(Paths.get("examples/authz"), "../../../lean"), args))
  * }}}
  */
object FrFlowCli:

  val usage: String =
    """Usage: <theory> <command> [args]
      |
      |Commands:
      |  lint                       check structure and coherence rules
      |  render                     generate Lean sources (model, obligations, assembly, audit)
      |  scaffold [NODE]            create or extend proof files with stubs for missing obligations
      |  check [NODE]               render, then verify with Lean and record results in the ledger
      |  status                     approval and verification status of every node
      |  approve NODE --by NAME     record human approval of a node's statement and model
      |  slice NODE [--stdout]      write the bounded theory slice for work on NODE
      |  digest                     write THEORY.md, the human-readable theory
      |""".stripMargin

  def run(theory: TheoryDef, ws: Workspace, args: Seq[String]): Int =
    val project = Project(theory.model, ws)
    args.toList match
      case "lint" :: Nil              => lint(project)
      case "render" :: Nil            => withLint(project)(render(project))
      case "scaffold" :: rest         => withLint(project)(scaffold(project, rest.headOption))
      case "check" :: rest            => withLint(project)(check(project, rest.headOption))
      case "status" :: Nil            => print(Reports.statusTable(project)); 0
      case "approve" :: id :: "--by" :: who :: Nil => approve(project, id, who)
      case "slice" :: id :: rest      => withLint(project)(slice(project, id, rest.contains("--stdout")))
      case "digest" :: Nil            => withLint(project)(digest(project))
      case _                          => System.err.println(usage); 2

  private def lint(project: Project): Int =
    val issues = project.lint()
    issues.foreach(i => println(i.render))
    val errs = Lints.errors(issues)
    println(s"${errs.size} error(s), ${issues.size - errs.size} warning(s)")
    if errs.isEmpty then 0 else 1

  private def withLint(project: Project)(body: => Int): Int =
    val issues = project.lint()
    issues.filter(_.severity == Severity.Warning).foreach(i => System.err.println(i.render))
    val errs = Lints.errors(issues)
    if errs.nonEmpty then
      errs.foreach(i => System.err.println(i.render))
      System.err.println("Lint errors must be fixed first.")
      1
    else body

  private def render(project: Project): Int =
    val res = project.render()
    res.created.foreach(f => println(s"created  lean/$f"))
    res.written.foreach(f => println(s"wrote    lean/$f"))
    res.removed.foreach(f => println(s"removed  lean/$f"))
    if res.created.isEmpty && res.written.isEmpty && res.removed.isEmpty then println("generated sources are up to date")
    0

  private def nodes(project: Project, only: Option[String]) =
    only match
      case Some(id) => project.theory.node(id).toSeq
      case None     => project.theory.topological

  private def scaffold(project: Project, only: Option[String]): Int =
    if only.exists(id => project.theory.node(id).isEmpty) then
      System.err.println(s"unknown node ${only.get}"); return 1
    project.render()
    nodes(project, only).foreach { n =>
      val added = project.scaffold(n)
      if added.nonEmpty then println(s"${n.id}: added stubs ${added.mkString(", ")} to lean/${project.renderer.proofsPath(n)}")
      else println(s"${n.id}: every obligation already has a theorem")
    }
    0

  private def check(project: Project, only: Option[String]): Int =
    if only.exists(id => project.theory.node(id).isEmpty) then
      System.err.println(s"unknown node ${only.get}"); return 1
    project.render()
    val runner = LeanRunner(project.ws.leanDir)
    if !runner.available then
      System.err.println("lake not found: install Lean (elan) or set FRFLOW_LAKE"); return 3
    val reports = Checker(project, runner).checkAndRecord(only)
    reports.foreach(printReport)
    println()
    print(Reports.statusTable(project))
    if reports.forall(_.verification.label == "proven") then 0 else 1

  private def printReport(rep: NodeReport): Unit =
    println(s"${rep.nodeId}: ${rep.verification.label} (${rep.proven}/${rep.obligations.size} obligations)")
    rep.obligations.filter(_.status != ObligationStatus.Proven).foreach { o =>
      println(s"  ${o.status.label.padTo(6, ' ')} ${o.name}${if o.detail.nonEmpty then s": ${o.detail}" else ""}")
    }
    rep.messages.foreach(m => println(s"  ! ${m.linesIterator.mkString("\n    ")}"))
    if rep.axioms.nonEmpty then
      val axs = rep.axioms.values.flatten.toSet.toSeq.sorted
      println(s"  axioms: ${if axs.isEmpty then "none" else axs.mkString(", ")}")

  private def approve(project: Project, id: String, who: String): Int =
    project.theory.node(id) match
      case None => System.err.println(s"unknown node $id"); 1
      case Some(n) =>
        val issues = Lints.errors(project.lint()).filter(_.nodeId.forall(_ == id))
        if issues.nonEmpty then
          issues.foreach(i => System.err.println(i.render))
          System.err.println("A node with lint errors cannot be approved."); 1
        else
          val h = project.hashes(id)
          val ledger = Ledger.load(project.ws).updated(id)(_.copy(approval = Some(Approval(h.spec, who, Instant.now().toString))))
          Ledger.save(project.ws, ledger)
          println(s"approved ${n.id} ${n.name} (spec ${h.spec.take(12)}) by $who")
          0

  private def slice(project: Project, id: String, stdout: Boolean): Int =
    project.theory.node(id) match
      case None => System.err.println(s"unknown node $id"); 1
      case Some(n) =>
        val text = Reports.slice(project, n)
        if stdout then print(text)
        else
          val path = project.ws.slicesDir.resolve(s"${n.id}.md")
          Files2.writeIfChanged(path, text)
          println(s"wrote ${project.ws.root.relativize(path)}")
        0

  private def digest(project: Project): Int =
    Files2.writeIfChanged(project.ws.digestFile, Reports.digest(project))
    println(s"wrote ${project.ws.root.relativize(project.ws.digestFile)}")
    0

  /** Convenience for `@main` methods: workspace root from `FRFLOW_ROOT` or a default. */
  def workspace(defaultRoot: String, kernelPath: String): Workspace =
    Workspace(Paths.get(sys.env.getOrElse("FRFLOW_ROOT", defaultRoot)).toAbsolutePath.normalize(), kernelPath)
