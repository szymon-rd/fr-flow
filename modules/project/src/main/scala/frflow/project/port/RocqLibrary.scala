package frflow.project.port

import cats.effect.Sync
import frflow.decision.content.Sha
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, LinkOption, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** FrFlow's Rocq library as a project's proofs load it: the directory holding it (`FrFlow/Base.v` in it), and its
  * version, a hash of every source of it, so a check made with another library is made again.
  */
final case class RocqLibrary(dir: Path, version: String)

object RocqLibrary:
  /** The library at `dir`, its sources read; of no such directory, a library with none (the prover then says so
    * when a check is asked).
    */
  def read[F[_]: Sync](dir: Path): F[RocqLibrary] = Sync[F].blocking {
    val files = (if Files.isDirectory(dir) then Using.resource(Files.walk(dir))(_.iterator.asScala.toList) else Nil)
      .filter(f => Files.isRegularFile(f, LinkOption.NOFOLLOW_LINKS) && f.toString.endsWith(".v"))
      .sortBy(dir.relativize(_).toString)
    RocqLibrary(dir, Sha.parts(files.flatMap(f => List(dir.relativize(f).toString, Files.readString(f, UTF_8)))*))
  }
