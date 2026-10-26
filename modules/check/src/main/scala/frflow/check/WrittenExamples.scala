package frflow
package check

import cats.effect.IO
import frflow.example.ExampleSuite
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** The examples written as tests of a knowledge base (`FrFlowExamples`): the suites compiled into the directories
  * `-Dfrflow.tests` names (the project's test classes), each built once and read.
  */
object WrittenExamples:
  def load(kb: KnowledgeBase): IO[KnowledgeBase] = IO.blocking {
    val suites = dirs.flatMap(classesIn).flatMap(suite).filter(_.knowledge.name == kb.name)
    if suites.isEmpty then kb else kb.withWritten(suites.flatMap(_.written))
  }

  private def dirs: List[Path] =
    sys.props.get("frflow.tests").toList.flatMap(_.split(java.io.File.pathSeparator)).filter(_.nonEmpty).map(Path.of(_))
      .filter(Files.isDirectory(_))

  /** The names of the top-level classes compiled under `dir`. */
  private def classesIn(dir: Path): List[String] =
    val files = Files.walk(dir)
    try files.iterator.asScala.map(dir.relativize(_).toString).filter(f => f.endsWith(".class") && !f.contains("$"))
      .map(_.stripSuffix(".class").replace(java.io.File.separatorChar, '.')).toList.sorted
    finally files.close()

  /** The suite a class is, built: one that is not loaded, abstract, or built with arguments is no suite of examples. */
  private def suite(name: String): Option[ExampleSuite] =
    val loader = Thread.currentThread.getContextClassLoader
    Try(Class.forName(name, false, loader)).toOption
      .filter(c => classOf[ExampleSuite].isAssignableFrom(c) && !java.lang.reflect.Modifier.isAbstract(c.getModifiers))
      .flatMap(c => Try(c.getDeclaredConstructor().newInstance().asInstanceOf[ExampleSuite]).toOption)
