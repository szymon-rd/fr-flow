package frflow.core

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** Every module's Scala sources under `modules/`, main and test, read for `ArchitectureSuite`. */
final class Sources(modules: Path):
  private val all: List[Source] = Using.resource(Files.walk(modules))(_.iterator.asScala.toList)
    .filter(p => p.toString.endsWith(".scala") && !p.toString.contains("/target/")).sorted.map(Source(modules, _))
  val main: List[Source] = all.filter(_.main)
  val tests: List[Source] = all.filterNot(_.main)
