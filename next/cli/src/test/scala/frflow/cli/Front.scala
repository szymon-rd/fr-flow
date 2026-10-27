package frflow.cli

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** What a front end's sources name of the shell: each `file: name`. */
object Front:
  private val Shell = """frflow\.(project|proof|testing|wire|api\.derive|api\.shell)\b""".r

  def named(rel: String): List[String] =
    val root = LazyList.iterate(Path.of("").toAbsolutePath)(_.getParent).takeWhile(_ != null).map(_.resolve(rel))
      .find(Files.isDirectory(_)).getOrElse(throw AssertionError(s"no $rel above ${Path.of("").toAbsolutePath}"))
    val files = Using.resource(Files.walk(root))(_.iterator.asScala.filter(_.toString.endsWith(".scala")).toList)
    assert(files.nonEmpty, root)
    files.sorted.flatMap(f => Shell.findAllIn(code(Files.readString(f, UTF_8))).map(m => s"${root.relativize(f)}: $m"))

  private val Strings = "(?s)\"\"\".*?\"\"\"|\"(?:[^\"\\\\\n]|\\\\.)*\"".r

  /** The text without its string literals: a name inside one (a build line `init` writes) is not a use. */
  private def code(text: String): String = Strings.replaceAllIn(text, "\"\"")
