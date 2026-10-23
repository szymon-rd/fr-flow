package frflow
package check

import frflow.ledger.Sha

/** The source files a node governs (a contract's implementation, a design decision's files),
  * and a hash of their content, to notice when they change.
  */
final case class Code(files: List[String], fingerprint: String)

object Code:
  /** The files under `paths` (directories are walked), named relative to `base`, so the fingerprint
    * is the same in every checkout.
    */
  def of(base: java.nio.file.Path, paths: List[java.nio.file.Path]): Code =
    import scala.jdk.CollectionConverters.*
    val files = paths.map(_.toAbsolutePath.normalize).flatMap { p =>
      if java.nio.file.Files.isDirectory(p) then java.nio.file.Files.walk(p, java.nio.file.FileVisitOption.FOLLOW_LINKS).iterator.asScala.filter(java.nio.file.Files.isRegularFile(_)).toList
      else List(p)
    }.distinct.map(p => base.toAbsolutePath.normalize.relativize(p).toString -> p).sortBy(_._1)
    val text = files.map((rel, p) => rel + "\u0000" + (if java.nio.file.Files.isRegularFile(p) then java.nio.file.Files.readString(p) else "<missing>"))
      .mkString("\u0000")
    Code(files.map(_._1), Sha(text))
