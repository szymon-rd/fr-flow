package frflow.api

import cats.effect.IO
import fs2.Stream
import frflow.api.shell.{Memory, ScriptedLean, Session}
import frflow.api.view.{CheckEvent, View}
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.rules.Command
import frflow.dsl.kb.KnowledgeBase
import frflow.project.Projects
import frflow.project.pipeline.Analysis
import frflow.project.program.Ports

/** Projects opened in memory for the API's suites: no Lean, git or disk. A session is opened over ports a test holds
  * (so two versions of a model can share one ledger, or a test can read the files written).
  */
object Opened:
  val sources: RelPath = Projects.sources
  val lean: Lean = Lean.Proving(Set.empty)

  def project(kb: KnowledgeBase): Project[IO] =
    Project(Projects.elaborated(kb), Nil, Nil, List(sources), "../../lean")

  lazy val before: Project[IO] = project(Shelf.Before.kb)
  lazy val after: Project[IO] = project(Shelf.After.kb)
  lazy val trusted: Project[IO] = project(Shelf.Trusted.kb)
  lazy val lone: Project[IO] = project(Shelf.Lone.kb)

  def api(p: Project[IO], decider: Option[String] = Some("ann"), lean: Lean = lean): IO[FrFlowApi[IO]] =
    FrFlowApi.inMemory(p, Map.empty, decider, lean)

  def ports(files: Map[RelPath, String] = Map.empty, decider: Option[String] = Some("ann")): IO[Ports[IO]] =
    Memory.ports[IO](files, decider)

  def session(p: Project[IO], ports: Ports[IO], lean: Lean = lean): Session[IO] =
    Session(p, ports, ScriptedLean[IO](lean), Memory.run)

  def over(p: Project[IO], ports: Ports[IO]): FrFlowApi[IO] = Memory.api(session(p, ports))

  def analysis(p: Project[IO], ports: Ports[IO]): IO[Analysis] = session(p, ports).analysis

  /** Every node checked (its code tested: untested code is not accepted), then accepted at once, parents first. */
  def acceptAll(api: FrFlowApi[IO]): IO[Unit] = checked(api.proving.check(None)).flatMap(v =>
    api.deciding.decide(Command.Accept(v.nodes.map(_.id), "it says what the service must do", Nil, Map.empty), "ann")
      .flatMap(out => IO.raiseUnless(out.isRight)(AssertionError(out.toString))))

  /** A check run to its end: its events. */
  def events(s: Stream[IO, CheckEvent]): IO[List[CheckEvent]] = s.compile.toList

  /** The view a check ends with. */
  def checked(s: Stream[IO, CheckEvent]): IO[View] = events(s).flatMap(_.collectFirst {
    case CheckEvent.Done(_, v) => v
  }.fold(IO.raiseError(AssertionError("no Done")))(IO.pure))

  def id(s: String): NodeId = NodeId(s)
