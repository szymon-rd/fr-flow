package frflow.core

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** Every module's Scala sources under `modules/`, main and test, read for `ArchitectureSuite`; or files given as
  * text, for its own tests.
  */
final class Sources(files: List[(String, String)]):
  private lazy val packages: Set[String] = all.filter(_.main).map(_.pkg).toSet
  private val all: List[Source] = files.map((rel, text) => Source(rel, text, packages))
  val main: List[Source] = all.filter(_.main)
  val tests: List[Source] = all.filterNot(_.main)

object Sources:
  def of(modules: Path): Sources = Sources(Using.resource(Files.walk(modules))(_.iterator.asScala.toList)
    .filter(p => p.toString.endsWith(".scala") && !p.toString.contains("/target/")).sorted
    .map(p => s"modules/${modules.relativize(p)}" -> Files.readString(p, UTF_8)))
