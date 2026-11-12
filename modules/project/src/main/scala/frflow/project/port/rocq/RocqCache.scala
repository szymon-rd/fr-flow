package frflow.project.port.rocq

import cats.effect.Sync
import frflow.decision.content.Sha
import frflow.proof.reading.RocqReport
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

/** What a build knows of one module once it is done with it: `stamp`, what a module importing it depends on (the
  * hash of what Rocq compiled it to; empty of one not run), and what Rocq said of it; none of one not run (a module
  * it imports did not go through whole) or stopped.
  */
final case class RocqBuilt(stamp: String, said: Option[RocqReport.File], timedOut: Boolean):
  /** Whether a module importing it may be run: Rocq read it whole, and accepted every proof in it. */
  def whole: Boolean = said.exists(f => f.broken.isEmpty && f.open.isEmpty)

/** The last build of each module, kept beside what it was compiled to: what it was a build of (`inputs`: Rocq's
  * version, the module's text, and the stamp of each module it imports), and what Rocq said. A module is compiled
  * again only when its inputs are not those (a file's time says nothing here), or when Rocq did not read it whole:
  * what broke it may be outside its inputs.
  */
final class RocqCache[F[_]: Sync](dirs: RocqDirs):
  def read(logical: String, inputs: String): F[Option[RocqBuilt]] = Sync[F].blocking {
    val (said, vo) = (dirs.said(logical), dirs.compiled(logical))
    Option.when(Files.isRegularFile(said))(Files.readString(said, UTF_8).split("\n", 3).toList).collect {
      case List(`inputs`, stamp, report) if Files.isRegularFile(vo) =>
        RocqBuilt(stamp, RocqReport.read(report).headOption, false)
    }.filter(_.said.exists(_.broken.isEmpty))
  }

  /** What Rocq said of a module it just compiled, kept when it read it whole, with the stamp of what it compiled it
    * to.
    */
  def write(logical: String, inputs: String, said: RocqReport.File): F[RocqBuilt] = Sync[F].blocking {
    val vo = dirs.compiled(logical)
    if said.broken.nonEmpty || !Files.isRegularFile(vo) then RocqBuilt("", Some(said), false)
    else
      val stamp = Sha.bytes(Files.readAllBytes(vo))
      Files.createDirectories(dirs.said(logical).getParent)
      Files.writeString(dirs.said(logical), List(inputs, stamp, RocqReport.print(List(said))).mkString("\n"), UTF_8)
      RocqBuilt(stamp, Some(said), false)
  }
