package frflow.core

/** A source file: its module, whether it is main, its package clauses, its code without comments and strings, and
  * what of FrFlow's packages it names: by their full name (`frflow.<module>…`, the facade `frflow.*` being eval's), or
  * relative to its own package, as Scala resolves a name a package clause makes visible (`outside.Guards` in
  * `frflow.core.analysis`: every package `packages` holds that the name can start).
  */
final class Source(val rel: String, text: String, packages: => Set[String]):
  private val parts = rel.split('/').toList.drop(1)
  val module: String = parts.head
  val main: Boolean = parts.lift(2).contains("main")
  val code: String = Source.code(text)
  val clauses: List[String] = Source.Package.findAllMatchIn(code).map(_.group(1)).toList
  val pkg: String = clauses.mkString(".")
  /** `module.package.File`, as architecture.conf names a place. */
  val name: String = (pkg.split('.').toList.drop(1) :+ parts.last.stripSuffix(".scala")).mkString(".")
  lazy val refs: List[Ref] = absolute ++ relative

  private def absolute: List[Ref] = Source.Named.findAllMatchIn(code).toList.flatMap(m =>
    (Option(m.group(1)), Option(m.group(2))) match
      case (Some(braced), _) => braced.split(",").toList.map(_.trim).filter(_.nonEmpty)
          .map(n => if n.head.isLower then Ref(s"frflow.${n.takeWhile(c => c.isLetterOrDigit || c == '_')}")
            else Ref("frflow"))
      case (None, Some(p))   => List(Ref(s"frflow.$p"))
      case (None, None)      => List(Ref("frflow")))

  /** Each prefix of the file's package (all of it, and what each further clause adds to) is a scope a relative name
    * is resolved in; a name starting with a package's last segment there names that package.
    */
  private def relative: List[Ref] =
    val scopes = clauses.inits.toList.filter(_.nonEmpty).map(_.mkString(".")).filter(_.startsWith("frflow"))
    Source.Word.findAllMatchIn(code).toList.flatMap(m =>
      scopes.map(s => s"$s.${m.group(1)}").find(packages).map(p => Ref(p + m.group(2))))

object Source:
  val Package = """(?m)^package ([\w.]+)""".r
  val Named = """\bfrflow\.(?:\{([^}]*)\}|([a-z]\w*(?:\.[a-z]\w*)*)|\*)""".r
  /** A name not reached through a dot, starting a path: `outside.Guards`, `rules.Refusal`. */
  val Word = """(?<![\w.])([a-z]\w*)((?:\.[a-z]\w*)*)\.[\w{*]""".r

  /** The text with comments and string literals blanked, so a word in either is not read as code. */
  def code(text: String): String =
    text.replaceAll("(?s)/\\*.*?\\*/", " ").replaceAll("(?s)\"\"\".*?\"\"\"", "\"\"").replaceAll("//[^\n]*", "")
      .replaceAll("\"(?:\\\\.|[^\"\\\\\n])*\"", "\"\"")
