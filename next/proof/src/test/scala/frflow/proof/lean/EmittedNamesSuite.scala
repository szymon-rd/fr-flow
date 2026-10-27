package frflow.proof.lean

import frflow.core.analysis.Reserved
import frflow.proof.lean.ast.Names
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Every name the lowering or the printer writes unescaped (`Names.builtin`, `Atoms.name`, `Atoms.const`,
  * `Names.path`, and FrFlow's own tactics and attributes) is a Lean keyword, a name of the prelude `Names.ident`
  * renames, or one `Reserved` refuses as a domain name: so no domain term (a Definition named `get`) can capture it.
  * Names Lean only binds or declares itself, never referring to a domain term in their scope, are listed apart.
  */
class EmittedNamesSuite extends munit.FunSuite:
  private val sources: Path =
    val here = Path.of(sys.props("user.dir")).toAbsolutePath
    List(here.resolve("next/proof/src/main/scala"), here.resolve("src/main/scala")).find(Files.isDirectory(_))
      .getOrElse(throw IllegalStateException(s"next-proof's sources are not under $here"))

  private def read(p: Path): String = Files.readString(p)
  private val files: List[Path] = Files.walk(sources).iterator.asScala.filter(_.toString.endsWith(".scala")).toList
  /** The sources without their comments, but the module layout's (module names, which no term mentions). */
  private val text: String = files.filterNot(_.endsWith("layout/Layout.scala")).map(read)
    .map(_.replaceAll("(?s)/\\*.*?\\*/", "").replaceAll("//[^\n]*", "")).mkString("\n")

  /** The literal names given to the makers of unescaped names, by their first part (the rest is qualified); of a
    * path, its first part only.
    */
  private val made: Set[String] =
    val call = """(?:builtin|Atoms\.name|\bname|Atoms\.const|\bconst)\(([^()]*)\)""".r
    val path = """Names\.path\(\s*"([A-Za-z_][A-Za-z0-9_']*)"""".r
    val literal = """"([A-Za-z_][A-Za-z0-9_'.]*)"""".r
    (call.findAllMatchIn(text).flatMap(m => literal.findAllMatchIn(m.group(1)).map(_.group(1).takeWhile(_ != '.'))) ++
      path.findAllMatchIn(text).map(_.group(1))).toSet
  /** FrFlow's own tactics, commands and attributes, named in fixed text. */
  private val own: Set[String] = """\bfrflow_\w+""".r.findAllIn(text).toSet
  /** What the printer writes in its fixed text of a `do` block: the handler of an error (`PrintDo`). */
  private val fixed: Set[String] = Set("tryCatchThe")

  /** Bound or declared by the generated Lean itself, inside a namespace of its own or a binder whose body names no
    * domain term unqualified: a lowering helper (`Naming.helper` avoids every taken name), a declaration of a node's
    * namespace (`claim`, `holds`), a named argument of FrFlow's library (`ε`, `init`), a hypothesis of fixed tactics.
    */
  private val local: Set[String] = Set("x", "s", "w", "k", "h", "_", "init", "ε", "claim", "holds", "complete",
    "impl", "root_impl", "refutes", "answer")

  test("every name written unescaped is a keyword, renamed, reserved, or bound by the generated Lean only") {
    val unsafe = (made ++ own ++ fixed)
      .filterNot(n => Names.Keywords(n) || Names.Prelude(n) || Reserved.names(n) || local(n))
    assertEquals(unsafe.toList.sorted, Nil, s"not reserved: ${unsafe.toList.sorted.mkString(", ")}")
  }

  test("the scan finds the names it is about") {
    assert(Set("pure", "get", "StateM", "frflow_defs", "frflow_witness", "World").subsetOf(made ++ own), made ++ own)
    assert(fixed.forall(w => files.exists(f => f.endsWith("print/PrintDo.scala") && read(f).contains(w))))
  }
