package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.{KeyStore, LedgerStore}
import frflow.protocol.{NodeKind as _, *}
import java.nio.file.Path
import java.security.PublicKey
import java.time.Instant

/** Everything the checker reads of the world, read once: the analysis is computed from it alone.
  *
  * @param idea     the idea file's text
  * @param checks   the recorded checks
  * @param proofs   the authored Lean files of the knowledge base (`lean/Proofs/<KB>/`), by name (a node's id,
  *                 or `Lemmas`)
  * @param texts    the files the nodes are written in, by the name a node gives (to show its definition)
  * @param code     the code each node governs, with its fingerprint
  * @param missing  the files nodes govern that do not exist
  * @param sources  the project's source files (see `Inputs.projectSources`), with their text
  * @param keys     the project's developer keys (`.frflow/keys`), which sign the decisions
  */
final case class Inputs(
    idea: String,
    ledger: Ledger,
    checks: Map[NodeId, NodeCheck],
    proofs: Map[String, String],
    texts: Map[String, String],
    code: Map[String, CodeRef],
    missing: Set[String],
    sources: Map[Path, String],
    keys: Map[KeyId, PublicKey],
    now: Instant)

object Inputs:
  val empty: Inputs = Inputs("", Ledger.empty, Map.empty, Map.empty, Map.empty, Map.empty, Set.empty, Map.empty, Map.empty, Instant.EPOCH)

  /** Reads the workspace, and the ledger from `ledger`. */
  def read(kb: KnowledgeBase, ws: Workspace, cfg: Config, ledger: LedgerStore): IO[Inputs] =
    (
      Disk.read(ws.root.resolve(kb.idea)).map(_.getOrElse("")),
      ledger.load,
      KeyStore.projectKeys(ws.keysDir),
      ChecksStore(ws.checksFile).load,
      proofs(kb, ws),
      texts(kb, ws),
      code(kb, ws),
      missing(kb, ws),
      projectSources(ws.root, cfg.sources).flatMap(_.traverse(p => Disk.read(p).map(p -> _.getOrElse("")))).map(_.toMap),
      IO.realTimeInstant
    ).parMapN { case (idea, ledger, keys, checks, proofs, texts, code, missing, sources, now) =>
      Inputs(idea, ledger, checks, proofs, texts, code, missing, sources, keys, now)
    }

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

  private def code(kb: KnowledgeBase, ws: Workspace): IO[Map[String, CodeRef]] =
    Code.governed(kb, ws.root).toList.traverse((id, paths) => Code.of(ws.root, paths).map(id -> _)).map(_.toMap)

  private def missing(kb: KnowledgeBase, ws: Workspace): IO[Set[String]] =
    kb.nodes.flatMap(_.governs).distinct.filterA(f => Disk.exists(ws.root.resolve(f)).map(!_)).map(_.toSet)

  /** The project's source files: every file under `src/main`, every source file elsewhere in the project
    * (but tests, builds' output, the Lean and FrFlow's own records), and every source the build compiles,
    * when the build names them: a source directory added in the build is production code too.
    */
  def projectSources(root0: Path, fromBuild: List[Path]): IO[List[Path]] =
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val root = abs(root0)
    // Only the project's own output and records are skipped, at its root: a `target` folder inside the
    // sources is compiled like any other. The build's own definitions (`project/*.scala`, `*.sbt`) are
    // code too: only their output is skipped.
    val skipDirs = Set("target", "lean", ".frflow", "node_modules")
    val codeExt = Set("scala", "sc", "sbt", "java", "kt", "js", "ts", "py", "go", "rs", "sql", "sh")
    def skipped(p: Path): Boolean =
      val name = p.getFileName.toString
      val parent = abs(p).getParent
      // Hidden directories are code like any other, but the tools' own at the root (.git, .bsp, ...).
      (name.startsWith(".") && parent == root) || (skipDirs(name) && parent == root) || root.relativize(abs(p)).toString == "src/test" ||
        ((name == "target" || name == "project") && parent == root.resolve("project"))
    def source(p: Path): Boolean =
      root.relativize(abs(p)).startsWith("src/main") || codeExt(p.getFileName.toString.reverse.takeWhile(_ != '.').reverse)
    def walk(dir: Path): IO[List[Path]] = Disk.list(dir).flatMap(_.flatTraverse { p =>
      Disk.isDirectory(p).flatMap(isDir =>
        if isDir then (if skipped(p) then IO.pure(Nil) else walk(p))
        else IO.pure(List(p).filter(source)))
    })
    val built = fromBuild.filterNot(p => abs(p).startsWith(root.resolve("target")))
    (walk(root).map(_ ++ built)).flatMap(_.filterA(Disk.isFile)).map(_.map(abs).distinct)
