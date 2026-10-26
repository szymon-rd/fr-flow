package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.{KeyStore, Store}
import frflow.protocol.*
import io.circe.Json
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.file.Path
import java.security.PublicKey
import java.time.Instant

/** Everything the checker reads, read once: `proofs` (`lean/Proofs/<KB>/`) by node id or `Lemmas`; `texts`, the nodes' files. */
final case class Inputs(idea: String, ledger: Ledger, checks: Map[NodeId, NodeCheck], proofs: Map[String, String],
    texts: Map[String, String], code: Map[String, CodeRef], missing: Set[String], sources: Map[Path, String],
    keys: Map[KeyId, PublicKey], now: Instant, tests: Map[NodeId, Recorded] = Map.empty,
    counterexamples: Map[NodeId, List[Counterexample]] = Map.empty, keyNames: Map[KeyId, String] = Map.empty,
    keyWarnings: List[String] = Nil)

object Inputs:
  val empty: Inputs = Inputs("", Ledger.empty, Map.empty, Map.empty, Map.empty, Map.empty, Set.empty, Map.empty, Map.empty, Instant.EPOCH)

  def read(kb: KnowledgeBase, ws: Workspace, cfg: Config, ledger: IO[Ledger]): IO[Inputs] =
    (if kb.idea.isEmpty then IO.pure("") else Disk.read(ws.root.resolve(kb.idea)).map(_.getOrElse("")), ledger, Keyring.read(ws).map(_._1), checks(ws.checksFile),
      proofs(kb, ws), texts(kb, ws), code(kb, ws.root),
      kb.nodes.flatMap(_.governs).distinct.filterA(f => Disk.exists(ws.root.resolve(f)).map(!_)).map(_.toSet),
      projectSources(ws.root, cfg.sources).flatMap(_.traverse(p => Disk.read(p).map(p -> _.getOrElse("")))).map(_.toMap),
      IO.realTimeInstant, Tests.recorded(ws.testsFile), Tests.counterexamples(ws.counterexamplesFile)
    ).parMapN { case (idea, ledger, keys, checks, proofs, texts, code, missing, sources, now, tests, counterexamples) =>
      Inputs(idea, ledger, checks, proofs, texts, code, missing, sources, keys.byId, now, tests, counterexamples, keys.names, keys.warnings)
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
      val impl = (kb.implementation(n).toList.flatMap(_.sources) ++ n.modelOf.toList.flatMap(_.impls).flatMap(_.sources))
        .filterNot(kb.modelFiles.contains).map(f => Path.of(f).toAbsolutePath.normalize)
        .filterNot(p => explicit.exists(g => p == g || p.startsWith(g)))
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
