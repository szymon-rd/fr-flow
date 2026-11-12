package frflow.dsl.compiled

import frflow.dsl.lifted.NotRead
import java.net.URLClassLoader
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.quoted.Quotes
import scala.tasty.inspector.{Inspector, Tasty, TastyInspector}
import scala.util.control.NonFatal

/** The TASTy of a compiled class, opened: the compiler writes a `.tasty` file beside each class file, holding
  * the class as it was typed, bodies included. `Inspect` reads the files of the place a class was loaded from (a
  * directory of classes, or a jar) and gives the compiler (`Compiler`) their trees. Nothing is compiled or run:
  * the trees are read, and the terms built from them.
  */
object Inspect:
  /** What `reading` makes of the TASTy `cls` was compiled into; Scala it does not read is a `NotRead`. */
  def apply[A](cls: Class[?])(reading: Quotes => A): A =
    val out = mutable.ListBuffer.empty[Either[Throwable, A]]
    val inspector = new Inspector:
      def inspect(using q: Quotes)(tastys: List[Tasty[q.type]]): Unit =
        out += (try Right(reading(q)) catch case NonFatal(e) => Left(e))
    val (files, jars) = written(cls)
    val read = try TastyInspector.inspectAllTastyFiles(files, jars, classpath(cls.getClassLoader))(inspector)
      catch case NonFatal(e) => throw NotRead(s"FrFlow: the TASTy of ${cls.getName} is not read: $e")
    out.headOption match
      case Some(Right(a))         => a
      case Some(Left(n: NotRead)) => throw n
      case Some(Left(other))      => throw NotRead(s"FrFlow: ${cls.getName} is not read from its TASTy: $other")
      case None                   => throw NotRead(s"FrFlow: ${cls.getName} has no TASTy where it was loaded " +
        s"from (read: $read): it is compiled by Scala 3 and its TASTy kept beside its class file")

  /** The TASTy files beside `cls`'s class file: every one of the directory it was loaded from, or its jar. */
  private def written(cls: Class[?]): (List[String], List[String]) =
    val from = Option(cls.getProtectionDomain.getCodeSource).map(s => Paths.get(s.getLocation.toURI))
      .getOrElse(throw NotRead(s"FrFlow: ${cls.getName} was not loaded from a directory or a jar"))
    if !Files.isDirectory(from) then (Nil, List(from.toString))
    else
      val all = Files.walk(from)
      try (all.iterator.asScala.map(_.toString).filter(_.endsWith(".tasty")).toList.sorted, Nil)
      finally all.close()

  /** The classpath `loader` and those above it load from, and the JVM's own: what the TASTy's names resolve in. */
  private def classpath(loader: ClassLoader): List[String] =
    val loaded = Iterator.iterate(loader)(_.getParent).takeWhile(_ != null).collect {
      case urls: URLClassLoader => urls.getURLs.toList.map(u => Paths.get(u.toURI): Path) }.flatten.toList
    (loaded.map(_.toString) ++ sys.props.getOrElse("java.class.path", "").split(java.io.File.pathSeparator))
      .filter(_.nonEmpty).distinct
