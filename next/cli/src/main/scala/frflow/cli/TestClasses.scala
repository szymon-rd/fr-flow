package frflow.cli

import cats.effect.IO
import cats.syntax.all.*
import frflow.dsl.example.FrFlowExamples
import java.lang.reflect.Modifier
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The examples written as tests, found where the build put a project's test classes (`-Dfrflow.tests`, which the
  * project's line in build.sbt sets): each concrete class extending `FrFlowExamples`, made with its no-argument
  * constructor. None without the property, or a directory there.
  */
object TestClasses:
  def examples(dir: Option[String]): IO[List[FrFlowExamples]] = dir.map(Path.of(_)).filter(Files.isDirectory(_))
    .fold(IO.pure(Nil))(d => IO.blocking(names(d).flatMap(made)))

  private def names(dir: Path): List[String] = Using.resource(Files.walk(dir))(_.iterator.asScala.toList)
    .map(dir.relativize(_).toString).filter(f => f.endsWith(".class") && !f.contains('$')).sorted
    .map(_.stripSuffix(".class").replace(java.io.File.separatorChar, '.'))

  private def made(name: String): Option[FrFlowExamples] =
    Either.catchNonFatal(Class.forName(name, false, getClass.getClassLoader)).toOption
      .filter(c => classOf[FrFlowExamples].isAssignableFrom(c) && !Modifier.isAbstract(c.getModifiers))
      .flatMap(c => Either.catchNonFatal(c.getDeclaredConstructor().newInstance()).toOption)
      .collect { case x: FrFlowExamples => x }

