package frflow.api

import java.lang.reflect.{Method, Modifier}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** Front ends depend on the API without seeing the shell (ARCHITECTURE.md, section 5: they see `api.view` and
  * `api.node` values only): no file they can reach (the algebras, `FrFlowApi`, the views) names a type of `project`,
  * `proof`, `testing` or `wire`, and no public member of one of their types has such a type in its signature; what
  * derives the views and interprets the algebras (`api.derive`, `api.shell`) is `private[api]` throughout, so a
  * front end cannot name it.
  */
class ArchitectureSuite extends munit.FunSuite:
  private val Shell = """frflow\.(project|proof|testing|wire)\b""".r
  private val Hidden = Set("derive", "shell")

  private val root: Path =
    val rel = Path.of("next/api/src/main/scala/frflow/api")
    LazyList.iterate(Path.of("").toAbsolutePath)(_.getParent).takeWhile(_ != null).map(_.resolve(rel))
      .find(Files.isDirectory(_)).getOrElse(fail(s"no $rel above ${Path.of("").toAbsolutePath}"))

  private val files: List[Path] = Using.resource(Files.walk(root))(_.iterator.asScala
    .filter(_.toString.endsWith(".scala")).toList.sorted)
  private def hidden(f: Path): Boolean = Hidden.contains(root.relativize(f).getName(0).toString)
  private def text(f: Path): String = Files.readString(f, UTF_8)

  test("no file a front end reaches names a type of project, proof, testing or wire") {
    val named = files.filterNot(hidden).flatMap(f => Shell.findFirstIn(text(f)).map(m => s"${root.relativize(f)}: $m"))
    assertEquals(named, Nil)
  }

  test("what derives the views and interprets the algebras is private to the API") {
    val TopLevel = """^(final |sealed |abstract )*(case class|class|trait|object|enum|def|val|type|given)\b.*""".r
    val open = files.filter(hidden).flatMap(f => text(f).linesIterator.collect {
      case l @ TopLevel(_*) => s"${root.relativize(f)}: $l"
    })
    assert(files.exists(hidden), files)
    assertEquals(open, Nil)
  }

  test("no public member of a type a front end reaches has a type of project, proof, testing or wire") {
    val classes = files.filterNot(hidden).flatMap(f => types(f)).flatMap(c => c :: c.getClasses.toList)
    val leaks = classes.flatMap(c => c.getMethods.toList.filter(m => Modifier.isPublic(m.getModifiers))
      .filter(m => Shell.findFirstIn(signature(m)).isDefined).map(m => s"${c.getName}.${m.getName}: ${signature(m)}"))
    assert(classes.size > 30, classes)
    assertEquals(leaks, Nil)
  }

  /** The classes a source file declares at its top level, and their companions. */
  private def types(f: Path): List[Class[?]] =
    val pkg = root.getParent.relativize(f.getParent).toString.replace('/', '.')
    val Decl = """^(?:final |sealed |abstract )*(?:case class|class|trait|object|enum) (\w+).*""".r
    text(f).linesIterator.collect { case Decl(name) => name }.toList.distinct
      .flatMap(n => List(s"frflow.$pkg.$n", s"frflow.$pkg.$n$$")).flatMap(c =>
        scala.util.Try(Class.forName(c)).toOption)

  private def signature(m: Method): String =
    (m.getGenericReturnType :: m.getGenericParameterTypes.toList).map(_.getTypeName).mkString(", ")
