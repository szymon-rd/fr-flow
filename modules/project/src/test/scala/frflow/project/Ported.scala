package frflow.project

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
import frflow.project.port.rocq.{RocqProver, RocqTool}
import frflow.project.process.{Command, Output}
import frflow.project.program.{Analyse, Ports, Project, TestProgram}
import frflow.testing.Settings
import frflow.testing.report.Outcome
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*
import scala.jdk.CollectionConverters.*

/** A model checked as `check` checks it, from cold, in a directory of its own: the developer's proofs written under
  * `rocq/Proofs`, Rocq run on every node and on the theory, the plain Scala tested with the default settings (1,000
  * cases from seed 1). What the suites tagged `Rocq` judge.
  */
object Ported:
  /** A fresh directory, removed after; or, for writing proofs, the one `FRFLOW_PORT_DIR` names, kept. */
  private val directory: Resource[IO, Path] = sys.env.get("FRFLOW_PORT_DIR").fold(
    Resource.make(IO.blocking(Files.createTempDirectory("frflow-port")))(d =>
      IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))))(d =>
    Resource.eval(IO.blocking(Files.createDirectories(Path.of(d)))))

  /** FrFlow's Rocq library, as the build keeps it. */
  lazy val library: Path = Projects.base.resolve("modules/proof/rocq")

  /** A project directory, and Rocq in its `rocq/`. */
  private val workspace: Resource[IO, (Path, Prover[IO])] = directory.flatMap(d =>
    RocqProver.make[IO](d.resolve("rocq"), library,
      RocqTool(Command("rocq", 30.minutes, Output.ByExit), RocqTool.Memory)).map(d -> _))

  /** The analysis once checked and tested; `proofs`, the developer's proof files by name (`Lemmas`, a node's). */
  def run(e: Elaborated, examples: List[Example], proofs: List[(String, String)]): IO[Analysis] =
    workspace.use { (dir, prover) =>
      val files = ProjectFiles.make[IO](dir)
      val code = RunCode.make[IO]
      val kb = e.theory.name.value
      for
        rocq    <- RocqLibrary.read[IO](library)
        ledger  <- MemoryLedger[IO](Ledger.empty)
        git     <- MemoryGit[IO]
        keys    <- MemoryKeys[IO]
        ports    = Ports(files, ledger, git, keys)
        _       <- proofs.traverse_((n, text) =>
                     files.writeIfChanged(RelPath.fromIdentifiers("rocq", s"Proofs/$kb/$n.v"), text))
        a       <- Analyse(ports, code, Project(Nil, Settings.default, rocq))(e, examples)
        (_, c)  <- CheckProgram(files, prover, code)(a, None)
        (_, t)  <- TestProgram[IO](files, code)(c, None)
      yield t
    }

  /** A resource's text, from the test class path. */
  def resource(path: String): String =
    scala.io.Source.fromResource(path, getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  /** The developer's proof files of an example, as its project keeps them (`examples/<example>/rocq/Proofs/<Kb>`),
    * by name.
    */
  def proofs(example: String, kb: String): List[(String, String)] =
    val dir = Projects.base.resolve(s"examples/$example/rocq/Proofs/$kb")
    val all = Files.list(dir)
    try all.iterator.asScala.toList.filter(_.toString.endsWith(".v")).sortBy(_.toString).map(p =>
      p.getFileName.toString.stripSuffix(".v") -> Files.readString(p))
    finally all.close()

  /** A node's standing as today's `standings.tsv` has it: kind, standing (proven, tested or assumed), its check's
    * status, and the cases its Scala was tested on.
    */
  def row(a: Analysis, id: NodeId): List[String] =
    val n = a.decided.theory.node(id).getOrElse(throw AssertionError(id.value))
    val status = a.current(id).fold("")(_.status.toString.toLowerCase)
    val checked = a.tested(id).filter(r => r.outcome match
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
