package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.protocol.{CodeRef, Fingerprint, Sha}
import java.nio.file.Path

/** The source files a node governs (a contract's implementation, a design decision's files),
  * and a hash of their content, to notice when they change.
  */
object Code:
  /** The paths each node governs: its `governs`, and the files of the code its implementation refers to
    * (not the model's file). Anything else the code depends on is governed explicitly (a design node owning
    * a directory), or `status` reports it as governed by no node.
    */
  def governed(kb: KnowledgeBase, root: Path): Map[String, List[Path]] =
    val explicit = kb.nodes.flatMap(_.governs).map(f => root.resolve(f).toAbsolutePath.normalize).toSet
    kb.nodes.map { n =>
      val impl = kb.implementation(n).toList.flatMap { i =>
        i.sources.filterNot(kb.modelFiles.contains).map(f => Path.of(f).toAbsolutePath.normalize)
          .filterNot(p => explicit.exists(g => p == g || p.startsWith(g)))
      }
      n.id -> (n.governs.map(root.resolve) ++ impl)
    }.filter(_._2.nonEmpty).toMap

  /** The files under `paths` (directories are walked), named relative to `base`, so the fingerprint
    * is the same in every checkout.
    */
  def of(base: Path, paths: List[Path]): IO[CodeRef] =
    val root = base.toAbsolutePath.normalize
    paths.map(_.toAbsolutePath.normalize).flatTraverse(Disk.files).flatMap { found =>
      found.distinct.map(p => root.relativize(p).toString -> p).sortBy(_._1)
        .traverse((rel, p) => Disk.read(p).map(rel -> _))
    }.map(fingerprint)

  /** The fingerprint of files read: (name, text, or none when missing). */
  def fingerprint(files: List[(String, Option[String])]): CodeRef =
    val text = files.map((rel, t) => rel + "\u0000" + t.getOrElse("<missing>")).mkString("\u0000")
    CodeRef(files.map(_._1), Fingerprint(Sha(text)))
