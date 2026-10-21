package frflow.cli

import frflow.Project
import frflow.check.{Checker, LeanRunner, NodeReport}
import frflow.dsl.Model
import frflow.ledger.{Approval, Ledger, ObligationStatus}
import frflow.lint.{Lints, Severity}
import frflow.report.Reports
import frflow.workspace.{Files2, Workspace}
import java.nio.file.Paths
import java.time.Instant

/** Command-line entry point. A model exposes it with:
  * {{{
  * @main def authz(args: String*): Unit =
  *   sys.exit(FrFlowCli.run(AuthzModel, FrFlowCli.workspace("examples/authz", "../../../lean"), args))
  * }}}
  */
object FrFlowCli:

  val usage: String =
    """Usage: <model> <command> [args]
      |
      |Nodes are `Theory` (domain and laws) and the layer ids.
      |
      |Commands:
      |  lint                       check structure and coherence rules
      |  render                     generate Lean from the Scala model
      |  check [NODE]               render, then verify with Lean and record results in the ledger
      |  scaffold NODE [--all]      add proof stubs for obligations automation did not prove (or all)
      |  status                     approval and verification status of every node
      |  approve NODE --by NAME     record human approval of a node's statement and model
      |  slice NODE [--stdout]      write the bounded context for work on NODE
      |  digest                     write THEORY.md, the human-readable theory
      |""".stripMargin

  def run(model: Model, ws: Workspace, args: Seq[String]): Int =
    val project = Project(model, ws)
    args.toList match
      case "lint" :: Nil                          => lint(project)
      case "render" :: Nil                        => withLint(project)(render(project))
      case "check" :: rest                        => withLint(project)(check(project, rest.headOption))
      case "scaffold" :: id :: rest               => withLint(project)(scaffold(project, id, rest.contains("--all")))
      case "status" :: Nil                        => print(Reports.statusTable(project)); 0
      case "approve" :: id :: "--by" :: who :: Nil => approve(project, id, who)
      case "slice" :: id :: rest                  => withLint(project)(slice(project, id, rest.contains("--stdout")))
      case "digest" :: Nil                        => withLint(project)(digest(project))
      case _                                      => System.err.println(usage); 2

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

  private def known(project: Project, id: String): Boolean =
    val ok = project.nodeIds.contains(id)
    if !ok then System.err.println(s"unknown node $id (nodes: ${project.nodeIds.mkString(", ")})")
    ok

  private def render(project: Project): Int =
    val res = project.render()
    res.created.foreach(f => println(s"created  lean/$f"))
    res.written.foreach(f => println(s"wrote    lean/$f"))
    res.removed.foreach(f => println(s"removed  lean/$f"))
    if res.created.isEmpty && res.written.isEmpty && res.removed.isEmpty then println("generated sources are up to date")
    0

  private def check(project: Project, only: Option[String]): Int =
    if only.exists(id => !known(project, id)) then return 1
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
    val auto = rep.obligations.count(_.detail == "auto")
    val authored = rep.obligations.count(_.detail == "authored")
    println(s"${rep.nodeId}: ${rep.verification.label} (${rep.proven}/${rep.obligations.size} obligations; $auto automatic, $authored authored)")
    rep.obligations.filter(_.status != ObligationStatus.Proven).foreach { o =>
      println(s"  ${o.status.label.padTo(6, ' ')} ${o.name}${if o.detail.nonEmpty then s": ${o.detail}" else ""}")
    }
    rep.messages.foreach(m => println(s"  ! ${m.linesIterator.mkString("\n    ")}"))
    if rep.axioms.nonEmpty then
      val axs = rep.axioms.values.flatten.toSet.toSeq.sorted
      println(s"  axioms: ${if axs.isEmpty then "none" else axs.mkString(", ")}")

  private def scaffold(project: Project, id: String, all: Boolean): Int =
    if !known(project, id) then return 1
    val names =
      if all then project.obligations(id).map(_.name)
      else
        val last = Ledger.load(project.ws).entry(id).lastCheck
          .filter(c => project.hashes.get(id).exists(_.check == c.checkHash))
        last match
          case None =>
            System.err.println(s"$id has no current check result: run `check $id` first, or pass --all"); return 1
          case Some(c) => c.obligations.filter(_.status != ObligationStatus.Proven).map(_.name)
    val added = project.scaffold(id, names)
    if added.isEmpty then println(s"$id: nothing to add")
    else
      println(s"$id: added stubs ${added.mkString(", ")} to lean/${project.renderer.proofsPath(id)}")
      project.render()
    0

  private def approve(project: Project, id: String, who: String): Int =
    if !known(project, id) then return 1
    val issues = Lints.errors(project.lint()).filter(_.nodeId.forall(_ == id))
    if issues.nonEmpty then
      issues.foreach(i => System.err.println(i.render))
      System.err.println("A node with lint errors cannot be approved."); 1
    else
      val h = project.hashes(id)
      val ledger = Ledger.load(project.ws).updated(id)(_.copy(approval = Some(Approval(h.spec, who, Instant.now().toString))))
      Ledger.save(project.ws, ledger)
      println(s"approved $id (spec ${h.spec.take(12)}) by $who")
      0

  private def slice(project: Project, id: String, stdout: Boolean): Int =
    if !known(project, id) then return 1
    val text = Reports.slice(project, id)
    if stdout then print(text)
    else
      val path = project.ws.slicesDir.resolve(s"$id.md")
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
