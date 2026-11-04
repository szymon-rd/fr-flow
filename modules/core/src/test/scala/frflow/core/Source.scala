package frflow.core

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** A source file: its module, whether it is main, its package, its code without comments and strings, and what of
  * FrFlow's packages it names (`frflow.<module>…`; the facade, `frflow.*`, is eval's).
  */
final class Source(modules: Path, path: Path):
  private val parts = modules.relativize(path).iterator.asScala.map(_.toString).toList
  val module: String = parts.head
  val main: Boolean = parts.lift(2).contains("main")
  val rel: String = s"modules/${parts.mkString("/")}"
  val code: String = Source.code(Files.readString(path, UTF_8))
  val pkg: String = Source.Package.findAllMatchIn(code).map(_.group(1)).mkString(".")
  /** `module.package.File`, as architecture.conf names a place. */
  val name: String = (pkg.split('.').toList.drop(1) :+ path.getFileName.toString.stripSuffix(".scala")).mkString(".")
  val refs: List[Ref] = Source.Named.findAllMatchIn(code).toList.flatMap(m =>
    (Option(m.group(1)), Option(m.group(2))) match
      case (Some(braced), _) => braced.split(",").toList.map(_.trim).filter(_.nonEmpty)
          .map(n => if n.head.isLower then Ref(s"frflow.${n.takeWhile(c => c.isLetterOrDigit || c == '_')}")
            else Ref("frflow"))
      case (None, Some(p))   => List(Ref(s"frflow.$p"))
      case (None, None)      => List(Ref("frflow")))

object Source:
  val Package = """(?m)^package ([\w.]+)""".r
  val Named = """\bfrflow\.(?:\{([^}]*)\}|([a-z]\w*(?:\.[a-z]\w*)*)|\*)""".r

  /** The text with comments and string literals blanked, so a word in either is not read as code. */
  def code(text: String): String =
    text.replaceAll("(?s)/\\*.*?\\*/", " ").replaceAll("(?s)\"\"\".*?\"\"\"", "\"\"").replaceAll("//[^\n]*", "")
      .replaceAll("\"(?:\\\\.|[^\"\\\\\n])*\"", "\"\"")
