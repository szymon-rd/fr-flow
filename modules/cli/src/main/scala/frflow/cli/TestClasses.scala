package frflow.cli

import cats.effect.IO
import cats.syntax.all.*
import frflow.api.view.NotMade
import frflow.dsl.example.FrFlowExamples
import java.lang.reflect.{InvocationTargetException, Modifier}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The examples written as tests, found where the build put a project's test classes (`-Dfrflow.tests`, which the
  * project's line in build.sbt sets): each concrete class extending `FrFlowExamples`, made with its no-argument
  * constructor (an `object`, as it is); and each such class that cannot be made, with why, so `status` says its
  * examples are not read. None without the property, or a directory there.
  */
object TestClasses:
  final case class Found(examples: List[FrFlowExamples], unread: List[(String, NotMade)])

  def examples(dir: Option[String]): IO[Found] = dir.map(Path.of(_)).filter(Files.isDirectory(_))
    .fold(IO.pure(Found(Nil, Nil)))(d => IO.blocking(in(d)))

  def in(dir: Path): Found =
    val found = names(dir).flatMap(n => examplesClass(n).map(n -> _)).map((n, c) => n -> made(c))
    Found(found.collect { case (_, Right(x)) => x }, found.collect { case (n, Left(why)) => n -> why })

  private def names(dir: Path): List[String] = Using.resource(Files.walk(dir))(_.iterator.asScala.toList)
    .map(dir.relativize(_).toString).filter(_.endsWith(".class")).sorted
    .map(_.stripSuffix(".class").replace(java.io.File.separatorChar, '.'))

  /** The class, if it is a concrete class of examples. */
  private def examplesClass(name: String): Option[Class[?]] =
    Either.catchNonFatal(Class.forName(name, false, getClass.getClassLoader)).toOption
      .filter(c => classOf[FrFlowExamples].isAssignableFrom(c) && !Modifier.isAbstract(c.getModifiers))

  private def made(c: Class[?]): Either[NotMade, FrFlowExamples] =
    val module = Either.catchNonFatal(c.getField("MODULE$")).toOption
    if c.isAnonymousClass then Left(NotMade.Anonymous)
    else module.fold(constructed(c))(f => call(f.get(null)))

  private def constructed(c: Class[?]): Either[NotMade, FrFlowExamples] =
    Either.catchNonFatal(c.getDeclaredConstructor()).toOption.fold(Left(
      if c.getEnclosingClass != null && !Modifier.isStatic(c.getModifiers) then NotMade.Nested
      else NotMade.NoConstructor))(k => call(k.newInstance()))

  private def call(make: => Any): Either[NotMade, FrFlowExamples] =
    Either.catchNonFatal(make).leftMap {
      case e: InvocationTargetException => NotMade.Threw(String.valueOf(e.getCause))
      case e                            => NotMade.Threw(String.valueOf(e))
    }.flatMap {
      case x: FrFlowExamples => Right(x)
      case other             => Left(NotMade.Threw(s"made a ${other.getClass.getName}"))
    }
