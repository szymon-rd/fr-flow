package frflow.project

import cats.effect.IO
import frflow.core.Elaborated
import frflow.core.analysis.Validate
import frflow.core.example.Example
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.{Counted, Ledger}
import frflow.dsl.kb.FrModel
import frflow.project.pipeline.{Analysis, Computed, Inputs, LeanSources, Recorded}
import frflow.project.port.memory.{MemoryFiles, MemoryGit, MemoryKeys, MemoryLedger}
import frflow.project.port.{LeanLibrary, RunCode}
import frflow.project.program.{Analyse, Ports, Project}
import frflow.proof.reading.ProofFile
import frflow.testing.Settings
import frflow.testing.report.Seed
import java.nio.file.{Files, Path}
import java.time.Instant
import scala.jdk.OptionConverters.*

/** Projects in memory for the shell's suites: a FrModel elaborated, its ports in memory (the files, the
  * ledger, git, a key made for the run), and its analysis as `Analyse` makes it.
  */
object Projects:
  /** Fewer cases than the default, so the suites stay quick; the seed is today's. */
  val settings: Settings = Settings(200, Seed(1))
  val sources: RelPath = RelPath.fromIdentifiers("src", "main")
  /** FrFlow's Lean library as the suites name it: no Lean runs on it in a unit suite. */
  val library: LeanLibrary = LeanLibrary("lean", "the library under test")
  val project: Project = Project(List(sources), settings, library)

  /** The build's base directory: the one holding `build.sbt` above these tests' classes, wherever they run from. */
  lazy val base: Path = Iterator.iterate(Path.of(getClass.getProtectionDomain.getCodeSource.getLocation.toURI))(
    _.getParent).takeWhile(_ != null).find(d => Files.exists(d.resolve("build.sbt")))
    .getOrElse(throw IllegalStateException("no build.sbt above the tests' classes"))

  /** A source file the code table names relative to the build (or, compiled elsewhere, by its name alone). */
  def source(file: RelPath): Path =
    val direct = base.resolve(file.value)
    if Files.isRegularFile(direct) then direct
    else List("modules", "examples").iterator.flatMap(d => Files.walk(base.resolve(d))
      .filter(p => Files.isRegularFile(p) && p.endsWith(file.value)).findFirst.toScala)
      .nextOption().getOrElse(throw IllegalStateException(s"no ${file.value} under $base"))

  def elaborated(kb: FrModel): Elaborated = kb.elaborated.fold(e => throw AssertionError(e.toString), identity)
  lazy val rooms: Elaborated = elaborated(_root_.rooms.rooms)
  lazy val roomsExamples: List[Example] =
    _root_.rooms.GrantedExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)

  /** The ports in memory, the files holding `files`; the key made for the run listed as `ann`'s. */
  final case class InMemory(ports: Ports[IO], files: MemoryFiles[IO], keys: MemoryKeys[IO], git: MemoryGit[IO])

  def inMemory(files: Map[RelPath, String]): IO[InMemory] =
    for
      f      <- MemoryFiles[IO](files)
      ledger <- MemoryLedger[IO](Ledger.empty)
      git    <- MemoryGit[IO]
      keys   <- MemoryKeys[IO]
      _      <- keys.list(keys.signed(frflow.decision.ledger.Deciders(List(keys.entry("ann")), None, None)))
    yield InMemory(Ports(f, ledger, git, keys), f, keys, git)

  def analysed(p: InMemory, e: Elaborated, examples: List[Example]): IO[Analysis] =
    Analyse(p.ports, RunCode.inline[IO], project)(e, examples)

  /** An analysis with nothing read: an empty ledger, nothing recorded, no examples run. */
  def bare(e: Elaborated): Analysis = proving(e, Map.empty)

  /** The same with proof files read: the obligations they prove are stated as theirs. */
  def proving(e: Elaborated, proofs: Map[NodeId, ProofFile]): Analysis =
    Analysis(Validate(e).fold(ps => throw AssertionError(ps.toString), identity),
      Inputs(Counted(Ledger.empty, Nil), Recorded.none, LeanSources(proofs, Nil, library.version), Map.empty,
        Instant.EPOCH, settings),
      Computed.none)
