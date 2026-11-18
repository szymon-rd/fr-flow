package frflow.web

import cats.effect.IO
import frflow.decision.content.Sha
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** What tells the page to read the project again: this process (`instance`, new each time `serve` starts, so a
  * server started again on a rebuilt model is noticed) and the files FrFlow keeps under `.frflow/` (a decision, a
  * request, a check). `reloads`: a supervisor (`bin/frflow-web`) starts the server again whenever the model's sources
  * change, so a changed model is being rebuilt rather than waiting for the developer to restart it.
  */
final case class Live(instance: String, directory: Path, reloads: Boolean):
  /** This process and the texts of the files directly under `.frflow/`, hashed together. */
  def version: IO[String] = IO.blocking {
    val kept = directory.resolve(".frflow")
    val files = if Files.isDirectory(kept) then Using.resource(Files.list(kept))(_.iterator.asScala.toList) else Nil
    files.filter(Files.isRegularFile(_)).sortBy(_.getFileName.toString)
      .flatMap(f => List(f.getFileName.toString, Files.readString(f)))
  }.map(texts => Sha.parts((instance :: texts)*))

object Live:
  /** The environment variable a supervisor sets: the server is started again on a rebuilt model. */
  val Reloads = "FRFLOW_WEB_RELOADS"

  def of(instance: String, directory: Path, env: Map[String, String]): Live =
    Live(instance, directory, env.get(Reloads).exists(_.nonEmpty))
