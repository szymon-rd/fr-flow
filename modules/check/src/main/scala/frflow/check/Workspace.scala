package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.{KeyStore, Store}
import frflow.protocol.*
import io.circe.Json
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{FileVisitOption, Files, Path}
import java.security.PublicKey
import java.time.Instant
import scala.concurrent.duration.*
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** Where a project lives: `lean/` (`FrFlowGen/` generated, `Proofs/` authored) and `.frflow/` (the ledger, requests and
  * keys committed; checks and snapshot derived). `kernelPath`: FrFlow's Lean kernel, relative to `lean/`.
  */
final case class Workspace(root: Path, kernelPath: String):
  def lean: Path = root.resolve("lean")
  def ledgerFile: Path = root.resolve(".frflow/ledger.json")
  def checksFile: Path = root.resolve(".frflow/checks.json")
  def snapshotFile: Path = root.resolve(".frflow/kb.json")
  def requestsFile: Path = root.resolve(".frflow/requests.json")
  def keysDir: Path = root.resolve(".frflow/keys")

/** How FrFlow runs, read once from the environment: `FRFLOW_LAKE`, `FRFLOW_TIMING` (print each Lean run's time),
  * `FRFLOW_THREADS` (the nodes of a level checked side by side), the developer's key (`FRFLOW_KEY`, or the one under
  * the home directory), who decides (`FRFLOW_AS`), and `-Dfrflow.sources` (every source the build compiles).
  */
final case class Config(lake: String, timing: Boolean, threads: Int, timeout: FiniteDuration, sources: List[Path], key: Path,
    as: Option[String])

object Config:
  def load(env: Map[String, String]): IO[Config] = IO(Config(
    lake = env.getOrElse("FRFLOW_LAKE", "lake"),
    timing = env.contains("FRFLOW_TIMING"),
    threads = env.get("FRFLOW_THREADS").flatMap(_.toIntOption).getOrElse(Runtime.getRuntime.availableProcessors.min(4)).max(1),
    timeout = 900.seconds,
    sources = sys.props.get("frflow.sources").toList.flatMap(_.split(java.io.File.pathSeparator)).filter(_.nonEmpty).map(Path.of(_)),
    key = KeyStore.keyFile(env, Path.of(sys.props.getOrElse("user.home", "."))),
    as = env.get("FRFLOW_AS").map(_.trim).filter(_.nonEmpty)))

  /** From the process's environment: for the tests. */
  def load: IO[Config] = IO(sys.env).flatMap(load(_))

/** The files the checker reads and writes (read whole, and written whole by the ledger's `Store`). */
object Disk:
  def read(p: Path): IO[Option[String]] = Store.read(p)

  /** Writes `text` unless the file already holds it; whether it wrote. */
  def update(p: Path, text: String): IO[Boolean] = read(p).flatMap(now =>
    if now.contains(text) then IO.pure(false) else IO.blocking { Files.createDirectories(p.getParent); Files.writeString(p, text, UTF_8) }.as(true))

  /** The entries of a directory, sorted; none when it is missing. */
  def list(dir: Path): IO[List[Path]] =
    IO.blocking(if !Files.isDirectory(dir) then Nil else Using.resource(Files.list(dir))(_.iterator.asScala.toList).sorted)

  /** The regular files under a directory (following links), or the path itself when it is a file. */
  def files(p: Path): IO[List[Path]] = IO.blocking(if !Files.isDirectory(p) then List(p)
    else Using.resource(Files.walk(p, FileVisitOption.FOLLOW_LINKS))(_.iterator.asScala.filter(Files.isRegularFile(_)).toList))

  def exists(p: Path): IO[Boolean] = IO.blocking(Files.exists(p))
  def isDirectory(p: Path): IO[Boolean] = IO.blocking(Files.isDirectory(p))
  def delete(p: Path): IO[Unit] = IO.blocking(Files.deleteIfExists(p)).void

/** Everything the checker reads, read once: `proofs` (`lean/Proofs/<KB>/`) by node id or `Lemmas`; `texts`, the nodes' files. */
final case class Inputs(idea: String, ledger: Ledger, checks: Map[NodeId, NodeCheck], proofs: Map[String, String],
    texts: Map[String, String], code: Map[String, CodeRef], missing: Set[String], sources: Map[Path, String],
    keys: Map[KeyId, PublicKey], now: Instant)

object Inputs:
  val empty: Inputs = Inputs("", Ledger.empty, Map.empty, Map.empty, Map.empty, Map.empty, Set.empty, Map.empty, Map.empty, Instant.EPOCH)

  def read(kb: KnowledgeBase, ws: Workspace, cfg: Config, ledger: IO[Ledger]): IO[Inputs] =
    (Disk.read(ws.root.resolve(kb.idea)).map(_.getOrElse("")), ledger, KeyStore.projectKeys(ws.keysDir), checks(ws.checksFile),
      proofs(kb, ws), texts(kb, ws), code(kb, ws.root),
      kb.nodes.flatMap(_.governs).distinct.filterA(f => Disk.exists(ws.root.resolve(f)).map(!_)).map(_.toSet),
      projectSources(ws.root, cfg.sources).flatMap(_.traverse(p => Disk.read(p).map(p -> _.getOrElse("")))).map(_.toMap),
      IO.realTimeInstant
    ).parMapN { case (idea, ledger, keys, checks, proofs, texts, code, missing, sources, now) =>
      Inputs(idea, ledger, checks, proofs, texts, code, missing, sources, keys, now)
    }

  /** The recorded checks (`.frflow/checks.json`, not committed); none when missing, or written by another version. */
  def checks(file: Path): IO[Map[NodeId, NodeCheck]] =
    Disk.read(file).map(_.flatMap(decode[Map[NodeId, NodeCheck]](_).toOption).getOrElse(Map.empty))

  def saveChecks(file: Path, checks: Map[NodeId, NodeCheck]): IO[Unit] =
    Store.writeJson(file, Json.fromFields(checks.toList.sortBy(_._1).map((id, c) => id.value -> c.asJson)))

  private def proofs(kb: KnowledgeBase, ws: Workspace): IO[Map[String, String]] =
    Disk.list(ws.lean.resolve(s"Proofs/${kb.name}"))
      .map(_.filter(_.getFileName.toString.endsWith(".lean")))
      .flatMap(_.traverseFilter(p => Disk.read(p).map(_.map(p.getFileName.toString.stripSuffix(".lean") -> _))))
      .map(_.toMap)

  /** The files the nodes are written in, by the name each node gives. */
  def texts(kb: KnowledgeBase, ws: Workspace): IO[Map[String, String]] =
    kb.nodes.filter(_.at >= 0).map(_.file).distinct.traverseFilter { f =>
      Disk.read(Path.of(f)).flatMap(t => t.fold(Disk.read(ws.root.resolve(f)))(x => IO.pure(Some(x)))).map(_.map(f -> _))
    }.map(_.toMap)

  /** The files each node governs (its `governs`, and those of its implementation but the model's), fingerprinted by their
    * names relative to `root`, the same in every checkout. Anything else the code uses is governed explicitly, or reported.
    */
  private def code(kb: KnowledgeBase, root: Path): IO[Map[String, CodeRef]] =
    val base = root.toAbsolutePath.normalize
    val explicit = kb.nodes.flatMap(_.governs).map(f => root.resolve(f).toAbsolutePath.normalize).toSet
    val governed = kb.nodes.map { n =>
      val impl = kb.implementation(n).toList.flatMap { i =>
        i.sources.filterNot(kb.modelFiles.contains).map(f => Path.of(f).toAbsolutePath.normalize)
          .filterNot(p => explicit.exists(g => p == g || p.startsWith(g)))
      }
      n.id -> (n.governs.map(root.resolve) ++ impl)
    }.filter(_._2.nonEmpty)
    governed.traverse { (id, paths) =>
      paths.map(_.toAbsolutePath.normalize).flatTraverse(Disk.files).flatMap { found =>
        found.distinct.map(p => base.relativize(p).toString -> p).sortBy(_._1).traverse((rel, p) => Disk.read(p).map(rel -> _))
      }.map { files =>
        val text = files.map((rel, t) => rel + "\u0000" + t.getOrElse("<missing>")).mkString("\u0000")
        id -> CodeRef(files.map(_._1), Fingerprint(Sha(text)))
      }
    }.map(_.toMap)

  /** Every file under `src/main` and every source the build compiles (production code too), but the build's output. */
  def projectSources(root: Path, fromBuild: List[Path]): IO[List[Path]] =
    val abs = (p: Path) => p.toAbsolutePath.normalize
    Disk.isDirectory(root.resolve("src/main")).ifM(Disk.files(root.resolve("src/main")), IO.pure(Nil)).map { main =>
      (main ++ fromBuild.filterNot(p => abs(p).startsWith(abs(root).resolve("target")))).map(abs).distinct
    }
