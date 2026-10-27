package frflow
package check

import cats.effect.IO
import frflow.ledger.Store
import frflow.protocol.*
import io.circe.Json
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.file.Path

/** Testing contracts' code against them as the checker does it: which nodes, what a result depends on, and its files. */
object Tests:
  /** How tests are made and run: a change to it runs every test again. */
  val Version: Int = 1
  /** At most this many failed cases kept per node. */
  private val Kept = 20

  def testable(a: Analysis): List[Node[?]] = a.kb.nodes.filter(Testing.tests(a.kb, _))

  /** What a node's test depends on: what it says (its Lean, through the definitions in force), its code, the settings
    * and the generators given.
    */
  def key(a: Analysis, n: Node[?]): Hash =
    val g = a.generate
    val lean = scala.util.Try(g.spec(n)).getOrElse("") + scala.util.Try(g.provenImpl(n).fold("")(_ => g.impl(n))).getOrElse("")
    Hash(Sha.parts(a.hash(n).value, lean, a.code(n).fold("")(_.fingerprint.value), settings(a).toString,
      a.kb.generators.map((t, gen) => s"${Types.scala(t)}: ${gen.describe}").mkString("\n"), Version.toString))

  def run(a: Analysis, n: Node[?], before: List[Counterexample]): IO[Option[TestReport]] =
    IO.blocking(a.kb.test(n, before.map(c => Testing.Replay(c.seed, c.index, c.size)), settings(a)).map(report))

  /** The FrModel's settings, with the seed `FRFLOW_SEED` gives for this run (a number, or `fresh`). */
  def settings(a: Analysis): TestSettings = TestSettings.inForce(a.kb.testing, sys.env.get("FRFLOW_SEED"))

  private def report(r: Testing.Report): TestReport =
    TestReport(r.cases, r.seed, r.against, r.failure.map(f => TestFailure(f.shown, f.why, f.seed, f.index, f.size)),
      r.coverage.map(c => Covered(c.part, c.held)), r.notes)

  /** The failed cases, with this run's added. */
  def kept(before: Map[NodeId, List[Counterexample]], found: List[(NodeId, TestReport)]): Map[NodeId, List[Counterexample]] =
    found.foldLeft(before) { case (acc, (id, r)) =>
      r.failure.fold(acc) { f =>
        val c = Counterexample(f.seed, f.index, f.size, f.shown)
        acc.updated(id, (c :: acc.getOrElse(id, Nil).filterNot(x => x.seed == c.seed && x.index == c.index)).take(Kept))
      }
    }

  def recorded(file: Path): IO[Map[NodeId, Recorded]] =
    Disk.read(file).map(_.flatMap(decode[Map[NodeId, Recorded]](_).toOption).getOrElse(Map.empty))
  def counterexamples(file: Path): IO[Map[NodeId, List[Counterexample]]] =
    Disk.read(file).map(_.flatMap(decode[Map[NodeId, List[Counterexample]]](_).toOption).getOrElse(Map.empty))

  def save(ws: Workspace, recorded: Map[NodeId, Recorded], counterexamples: Map[NodeId, List[Counterexample]]): IO[Unit] =
    Store.writeJson(ws.testsFile, Json.fromFields(recorded.toList.sortBy(_._1).map((id, r) => id.value -> r.asJson))) *>
      (if counterexamples.isEmpty then IO.unit
       else Store.writeJson(ws.counterexamplesFile, Json.fromFields(counterexamples.toList.sortBy(_._1).map((id, cs) => id.value -> cs.asJson))))
