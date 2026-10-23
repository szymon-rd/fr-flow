package frflow
package cli

import frflow.check.*
import frflow.lean.*
import frflow.ledger.*
import cats.effect.IO
import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.protocol.{CheckStatus, NodeCheck, ObligationStatus}
import java.nio.file.Paths

/** Command line of a kb, which a project's main object runs through `frflow.cli.FrFlowApp`. */
object Cli:
  val usage: String =
    """Usage: <kb> <command>
      |
      |  render                  generate Lean and the snapshot .frflow/kb.json from the Scala definitions
      |  check [NODE]            render, prove each node from its parts, record the results
      |  status                  the tree: decisions, proofs, examples, what is trusted; exits 1 unless the knowledge base is complete
      |  ci                      for CI: check, then status; exits 1 unless everything is proven and decided
      |  inbox                   start here: the developer's open requests, what is yours to do, what waits for the developer
      |  context NODE            everything needed to work on NODE (for agents and people)
      |  find WORDS|PATH         the nodes that govern a file, or what mentions some words (nodes, reasons, rejected options, the idea)
      |  scaffold NODE           a proof file for an obligation automation did not prove
      |  answer REQUEST TEXT     reply to the developer's request; with a NODE instead, tell them about work they did not ask for
      |
      |Decisions are the developer's.
      |""".stripMargin

  def run(kb: KnowledgeBase, ws: Workspace, args: Seq[String]): Int =
    val problems = kb.problems ++ Generate.problems(kb)
    if problems.nonEmpty then
      IO(problems.foreach(p => System.err.println(s"error: $p"))).as(1).unsafeRunSync()
    else Workflow(kb, ws).flatMap(w => command(kb, ws, w, args.toList)).unsafeRunSync()

  private def err(s: String): IO[Unit] = IO(System.err.println(s))
  private def out(s: String): IO[Unit] = IO(println(s))

  private def command(kb: KnowledgeBase, ws: Workspace, w: Workflow, args: List[String]): IO[Int] =
    def node(id: String)(f: Node[?] => IO[Int]): IO[Int] = kb.node(id).fold(err(s"unknown node $id").as(1))(f)
    def withLake(f: IO[Int]): IO[Int] = w.lake.available.ifM(f, err("lake not found (set FRFLOW_LAKE)").as(3))
    args match
      case "check" :: rest =>
        withLake(rest.headOption.filter(kb.node(_).isEmpty).fold(
          for
            checked <- w.check(rest.headOption)
            _ <- w.writeSnapshot(checked.after)
            failing <- checked.results.traverse((n, c) => out(checkText(kb, n, c)).as(failingExamples(kb, n).nonEmpty))
            _ <- out("")
            _ <- IO(print(Status.text(Status.of(checked.after))))
          yield if checked.allProven && !failing.contains(true) then 0 else 1
        )(id => err(s"unknown node $id").as(1)))
      case "ci" :: Nil =>
        withLake(w.ci.flatMap { ci =>
          ci.checked.results.filter(_._2.status != CheckStatus.Proven).traverse_((n, c) => out(s"${n.id}: ${c.status}")) *>
            IO(print(Status.text(ci.status))).as(if ci.ok then 0 else 1)
        })
      case "render" :: Nil =>
        for
          a <- w.analysis
          changed <- w.render(a)
          file <- w.writeSnapshot(a)
          _ <- out(s"rendered ${changed.size} changed file(s); wrote ${ws.root.relativize(file)}")
        yield 0
      // The snapshot is written too, so it shows what status says.
      case "status" :: Nil =>
        w.analysis.flatMap(a => w.writeSnapshot(a) *> IO(Status.of(a)).flatMap(s => IO(print(Status.text(s))).as(if s.ok then 0 else 1)))
      case "inbox" :: Nil => (w.analysis, w.stores.requests.load.map(_.filter(_.status == frflow.protocol.RequestStatus.Open))).parTupled.flatMap((a, rs) => out(Reports.inbox(Some(a.annotated), rs))).as(0)
      case "context" :: id :: Nil => node(id)(n => w.context(n).flatMap(c => IO(print(c.text))).as(0))
      case "find" :: query if query.nonEmpty => w.analysis.flatMap(a => out(Reports.find(a.annotated, query.mkString(" ")))).as(0)
      case "scaffold" :: id :: Nil =>
        node(id) { n =>
          w.scaffold(n).flatMap(f => out(f.fold("nothing to create")(f => s"created $f"))) *> w.writeSnapshot.as(0)
        }
      case "answer" :: to :: text if text.nonEmpty =>
        w.stores.requests.answer(to, text.mkString(" "), id => kb.node(id.value).isDefined).flatMap {
          case Right(r) => out(s"answered ${r.id}").as(0)
          case Left(e) => err(e.message).as(1)
        }
      case _ => err(usage).as(2)

  private def failingExamples(kb: KnowledgeBase, n: Node[?]) =
    kb.exampleResults(n).filter(r => r.contract != "ok" || r.implementation.exists(_ != "ok"))

  /** A node's check: its status, with what else is open, and failing examples first: they show the code
    * (or the contract) is wrong, which no proof fixes.
    */
  private def checkText(kb: KnowledgeBase, n: Node[?], c: NodeCheck): String =
    val open = c.obligations.filter(r => !r.isEvaluation && !r.fine)
    val failing = failingExamples(kb, n)
    (List(s"${n.id}: ${c.status}${if c.status == CheckStatus.Proven && open.nonEmpty then s" (not proven: ${open.map(_.name).mkString(", ")})" else ""}") ++
      (if failing.isEmpty then Nil
       else s"  ${failing.size} example(s) fail: the code or the contract is wrong; fix that, not the proof" ::
         failing.take(5).map(r => s"    ${r.example.describe}: ${r.verdict}")) ++
      // `idle` is not an obligation: proven, it says the root is met by doing nothing.
      c.obligations.filter(r => !r.fine).map(r => s"  ${r.status} ${r.name}: ${r.detail.linesIterator.mkString("\n    ")}") ++
      c.obligations.filter(r => r.name == "idle" && r.status == ObligationStatus.Idle).map(r =>
        s"  ! doing nothing meets it (${r.detail}): state what users can do, so it says exactly what the system does (status fails until then)") ++
      // With an example failing, the node may be false: no hint to prove it.
      c.messages.filterNot(m => failing.nonEmpty && m.startsWith("prove it in")).map(m => s"  ! ${m.linesIterator.mkString("\n    ")}")).mkString("\n")

  /** The workspace at `FRFLOW_ROOT`, or `default`; `kernelPath` is relative to its `lean/`. */
  def workspace(default: String, kernelPath: String): Workspace =
    Workspace(Paths.get(sys.env.getOrElse("FRFLOW_ROOT", default)).toAbsolutePath.normalize, kernelPath)
