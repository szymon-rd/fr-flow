package frflow.api

import java.nio.charset.StandardCharsets.{ISO_8859_1, UTF_8}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using
import scala.util.matching.Regex

/** What a front end names of what it must not see, each as `file: name`: in its sources (outside string literals and
  * comments, however the import is spelled) and in its compiled classes (whatever the source's spelling).
  */
object Front:
  /** The shell's packages: named in full, in an import's braces, or from a wildcard import of `frflow`. */
  val Shell: Regex = ("""frflow\s*\.\s*(project|proof|testing|wire|api\s*\.\s*(derive|shell))\b|""" +
    """frflow\s*\.\s*\{[^}]*\b(project|proof|testing|wire)\b|frflow\s*\.\s*api\s*\.\s*\{[^}]*\b(derive|shell)\b|""" +
    """import\s+frflow\s*\.\s*[*_]""").r

  /** The shell's packages as compiled classes name them. */
  val ShellClasses: Regex = "frflow/(project|proof|testing|wire|api/derive|api/shell)/".r

  /** Each name `forbidden` matches in the sources under `rel` (a directory of the build). */
  def named(rel: String, forbidden: Regex = Shell): List[String] =
    val root = LazyList.iterate(Path.of("").toAbsolutePath)(_.getParent).takeWhile(_ != null).map(_.resolve(rel))
      .find(Files.isDirectory(_)).getOrElse(throw AssertionError(s"no $rel above ${Path.of("").toAbsolutePath}"))
    found(root, ".scala", forbidden, f => code(Files.readString(f, UTF_8)))

  /** Each name `forbidden` matches in the classes compiled with `of` (its module's, not its tests'). */
  def compiled(of: Class[?], forbidden: Regex = ShellClasses): List[String] =
    val root = Path.of(of.getProtectionDomain.getCodeSource.getLocation.toURI)
    found(root, ".class", forbidden, f => String(Files.readAllBytes(f), ISO_8859_1))

  private def found(root: Path, suffix: String, forbidden: Regex, text: Path => String): List[String] =
    val files = Using.resource(Files.walk(root))(_.iterator.asScala.filter(_.toString.endsWith(suffix)).toList)
    assert(files.nonEmpty, root)
    files.sorted.flatMap(f => forbidden.findAllIn(text(f)).toList.distinct.map(m => s"${root.relativize(f)}: $m"))

  private val Strings = "(?s)\"\"\".*?\"\"\"|\"(?:[^\"\\\\\n]|\\\\.)*\"".r
  private val Comments = "(?s)/\\*.*?\\*/|//[^\n]*".r

  /** The text without its string literals and comments: a name inside one (a build line `init` writes) is not a use. */
  def code(text: String): String = Comments.replaceAllIn(Strings.replaceAllIn(text, "\"\""), "")
