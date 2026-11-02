package frflow.project

import cats.data.NonEmptyList
import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.example.Example
import frflow.core.name.{NodeId, RelPath}
import frflow.core.spec.NodeKind
import frflow.decision.ledger.Ledger
import frflow.project.check.CheckProgram
import frflow.project.pipeline.{Analysis, ReadProof}
import frflow.project.port.*
import frflow.project.port.memory.*
import frflow.project.process.{Command, Output}
import frflow.project.program.{Analyse, ModelCheck, Ports, Project, TestProgram}
import frflow.proof.lean.ast.{ModuleName, Names}
import frflow.proof.layout.LeanWorkspace
import frflow.proof.verdict.ProverRun
import frflow.testing.Settings
import frflow.testing.report.Outcome
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** An example ported, checked as `check` checks it, from cold: the developer's proofs written under `lean/Proofs`,
  * Lean run on every node and on the theory, the plain Scala tested with the default settings (1,000 cases from seed
  * 1, as today); then, with today's Lean beside it under `FrFlowGen/Old`, the module stating each claim equivalent to
  * today's built. What each port's `PortSuite` judges.
  */
object Ported:
  /** The analysis once checked and tested, and how Lean built the equivalences, if any were given. */
  final case class Run(analysis: Analysis, port: Option[ProverRun])

  /** What a port gives Lean: its proofs (by name, under `lean/Proofs/<Kb>`), today's modules and the module stating
    * the equivalences (by path under `lean/`), and the module to build of those.
    */
  final case class Lean(proofs: List[(String, String)], old: List[(String, String)], port: Option[String])

  private val directory: Resource[IO, Path] = Resource.make(IO.blocking(Files.createTempDirectory("frflow-port")))(
    d => IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p))))

  private def module(name: String): ModuleName = ModuleName(Names.path(name.split('.').toList*))

  /** A project directory, and Lake in its `lean/`. */
  private val workspace: Resource[IO, (Path, Lake[IO])] =
    directory.flatMap(d => Lake.make[IO](d.resolve("lean"), Command("lake", 30.minutes, Output.Merged)).map(d -> _))

  def run(e: Elaborated, examples: List[Example], lean: Lean, models: List[ModelCheck[IO]]): IO[Run] =
    workspace.use { (dir, lake) =>
      val files = ProjectFiles.make[IO](dir)
      val code = RunCode.make[IO]
      def write(path: String, text: String) = files.writeIfChanged(RelPath.fromIdentifiers("lean", path), text)
      val kb = e.theory.name.value
      for
        library <- LeanLibrary.read[IO](LeanWorkspace.library, LeanWorkspace.library.toString)
        ledger  <- MemoryLedger[IO](Ledger.empty)
        git     <- MemoryGit[IO]
        keys    <- MemoryKeys[IO]
        ports    = Ports(files, ledger, git, keys)
        _       <- lean.proofs.traverse_((n, text) => write(s"Proofs/$kb/$n.lean", text))
        a       <- Analyse(ports, code, Project(Nil, Settings.default, library))(e, examples)
        (_, c)  <- CheckProgram(files, lake, library.path, code)(a, None)
        (_, t)  <- TestProgram[IO](files, code, models)(c, None)
        _       <- lean.old.traverse_((p, text) => write(p, text))
        built   <- lean.port.traverse(p => lake.build(NonEmptyList.one(module(p))))
      yield Run(t, built)
    }

  /** The Definitions given a value provided where the code runs (`implementProvided`), by name: what each port
    * judges under owner §45 D (a value standing for "now" or the history so far, in statements about the state over
    * time, is the World's; configuration fixed for the run stays provided).
    */
  def provided(e: Elaborated): Set[String] =
    e.theory.code.attached.collect { case (s, a) if a.code == frflow.core.code.Code.Provided => s.value }.toSet

  /** How a value provided where the code runs stands under owner §45 D ("the clock and histories that crm, keycloak
    * and auth read as provided values are modelled as part of the World"): done only where none is `Stopped`.
    */
  enum OnD:
    /** Configuration, fixed for the run: not "now" or a history, which D names; stays provided. */
    case Configuration(why: String)
    /** "Now" or the history so far, the World's under D, not moved: the step stops on a design point (`on`), D not
      * done for it.
      */
    case Stopped(on: String, why: String)
    /** D names the value, and the owner ruled it stays provided (`by`, a decision of his). */
    case Ruled(by: String, why: String)

  /** The values D is not done for: each stopped one, with the point it waits on. */
  def stoppedOnD(judged: Map[String, OnD]): Map[String, String] =
    judged.collect { case (v, OnD.Stopped(on, _)) => v -> on }

  /** A resource's text, from the test class path. */
  def resource(path: String): String =
    scala.io.Source.fromResource(path, getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  /** A node's standing as today's `standings.tsv` has it: kind, standing (proven, tested or assumed), its check's
    * status, and the cases its Scala was tested on; a model's runs shown beside its `onlyCodeChanges` assumption.
    */
  def row(a: Analysis, id: NodeId): List[String] =
    val n = a.decided.theory.node(id).getOrElse(throw AssertionError(id.value))
    val status = a.current(id).fold("")(_.status.toString.toLowerCase)
    val model = Option.when(n.statement.kind == NodeKind.Assumption)(a.models(id)).toList.flatten
    val checked = a.tested(id).orElse(model.headOption.flatMap(a.testedModel)).filter(r => r.outcome match
      case Outcome.NotChecked(_) => false
      case _                     => true)
    val standing = n.statement.kind match
      case NodeKind.Assumption => "assumed"
      case NodeKind.Design     => "nothing to prove"
      case NodeKind.Claim      => checked.fold(status)(_ => "tested")
    List(n.statement.kind.toString.toLowerCase, standing, status, checked.fold("")(_.cases.toString))

  /** What of each node is not proven, as `status` reads it: none of a node that stands. */
  def unproven(a: Analysis): Map[String, List[String]] =
    a.decided.theory.nodes.map(_.node).map(n => n.id.value -> ReadProof.of(a, n).unproven.map(_.toString))
      .filter(_._2.nonEmpty).toMap

  /** Each node's standing and, where its check found something, what: for a failing suite's message. */
  def table(a: Analysis): String =
    a.decided.theory.nodes.map(_.node.id).sortBy(_.value).map { id =>
      val found = a.current(id).toList.flatMap(c => c.findings.map(_.toString.take(600)) ++
        c.results.filter(r => r.status != frflow.proof.verdict.ObligationStatus.Proven).map(r =>
          s"${r.name} ${r.status} ${r.messages.map(_.toString.take(300)).mkString(" | ")}"))
      (id.value.capitalize :: row(a, id)).mkString("\t") + found.map("\n    " + _).mkString
    }.mkString("\n")
