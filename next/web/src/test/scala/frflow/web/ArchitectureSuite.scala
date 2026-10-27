package frflow.web

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The web view is a front end: it sees the API's views and algebras (and the core, DSL, decision and eval values
  * they carry), never the shell. No source of it, outside its string literals, names `frflow.project`,
  * `frflow.proof`, `frflow.testing` or `frflow.wire`, nor the API's own `derive` and `shell`; nor the command line,
  * which it does not depend on.
  */
class ArchitectureSuite extends munit.FunSuite:
  private val Shell = """frflow\.(project|proof|testing|wire|api\.derive|api\.shell|cli)\b""".r
  private val Strings = "(?s)\"\"\".*?\"\"\"|\"(?:[^\"\\\\\n]|\\\\.)*\"".r

  test("no source of the web view names project, proof, testing, wire, the API's derive and shell, or the CLI") {
    val rel = Path.of("next/web/src/main/scala/frflow/web")
    val root = LazyList.iterate(Path.of("").toAbsolutePath)(_.getParent).takeWhile(_ != null).map(_.resolve(rel))
      .find(Files.isDirectory(_)).getOrElse(fail(s"no $rel"))
    val files = Using.resource(Files.walk(root))(_.iterator.asScala.filter(_.toString.endsWith(".scala")).toList)
    assert(files.size > 5, files)
    val named = files.sorted.flatMap(f => Shell.findAllIn(Strings.replaceAllIn(Files.readString(f, UTF_8), "\"\""))
      .map(m => s"${root.relativize(f)}: $m"))
    assertEquals(named, Nil)
  }
