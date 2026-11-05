package frflow.project.port

import cats.effect.Sync
import frflow.decision.content.Sha
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, LinkOption, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** FrFlow's Lean library as a project's Lean requires it: its path, as `lean/lakefile.toml` names it (relative to
  * `lean/`, or absolute), and its version, a hash of every file of it Lean reads (its sources, its lakefile and
  * toolchain), so a check made with another library is checked again.
  */
final case class LeanLibrary(path: String, version: String)

object LeanLibrary:
  /** The library at `dir`, required as `path`: its files read, `.lake` (its build) left out; none where there is no
    * such directory (Lake then says so when a check is asked).
    */
  def read[F[_]: Sync](dir: Path, path: String): F[LeanLibrary] = Sync[F].blocking {
    val files = (if Files.isDirectory(dir) then Using.resource(Files.walk(dir))(_.iterator.asScala.toList) else Nil)
      .filter(f => Files.isRegularFile(f, LinkOption.NOFOLLOW_LINKS) && !dir.relativize(f).startsWith(".lake"))
      .filter(f => f.toString.endsWith(".lean") || Set("lakefile.toml", "lean-toolchain")(f.getFileName.toString))
      .sortBy(dir.relativize(_).toString)
    LeanLibrary(path, Sha.parts(files.flatMap(f => List(dir.relativize(f).toString, Files.readString(f, UTF_8)))*))
  }
