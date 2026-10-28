package rooms

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** What today's library recorded of rooms (`reference/rooms`, captured at 526fe35): each node's standing, where it
  * sits and what it assumes as `show` printed them, and its Lean, put in namespace `Old` over the port's types so
  * the port's claims can be stated equivalent to today's.
  */
object Reference:
  val dir: Path = Path.of("reference/rooms")

  private def lines(p: Path): List[String] = Files.readAllLines(p).asScala.toList

  /** Each node's standing (`standings.tsv`): kind, standing, status, cases, by its id capitalized. */
  def standings: Map[String, List[String]] =
    lines(dir.resolve("standings.tsv")).drop(1).map(_.split("\t", -1).toList)
      .map(cs => cs.head -> List(cs(1), cs(2), cs(3), cs(6))).toMap

  /** The nodes `show` printed, by id. */
  def nodes: List[String] = Files.list(dir.resolve("show")).iterator.asScala.toList.map(_.getFileName.toString)
    .filter(_.endsWith(".txt")).map(f => f.stripSuffix(".txt")).map(n => n.head.toLower +: n.tail).sorted

  /** The ids `show` listed under a section of a node's page (`Parts…`, `Assumes`), in order. */
  def section(node: String, title: String): List[String] =
    val page = lines(dir.resolve("show").resolve(node.capitalize + ".txt"))
    page.dropWhile(l => !l.startsWith(title)).drop(1).takeWhile(_.startsWith("  ")).map(_.trim)
      .filter(l => l.startsWith("+ ") || l.startsWith("- ") || l.startsWith("x ") || l.startsWith("o "))
      .map(_.drop(2).takeWhile(c => !c.isWhitespace))

  def parts(node: String): List[String] = section(node, "Parts")
  def assumes(node: String): List[String] = section(node, "Assumes")

  /** Today's Lean of rooms' words and statements (the domain's defines and each node's `Spec`), in namespace `Old`
    * and over the port's types and boundary: by path under `FrFlowGen/Old`.
    */
  def oldLean: List[(String, String)] =
    val root = dir.resolve("lean/FrFlowGen/Rooms")
    Files.walk(root).iterator.asScala.toList.filter(Files.isRegularFile(_)).map(p => root.relativize(p).toString)
      .filter(r => r.startsWith("Domain") || r.endsWith("/Spec.lean")).sorted
      .map(r => r -> old(Files.readString(root.resolve(r))))

  /** `Rooms.` named `Old.`, the port's types and boundary imported in place of today's and opened. */
  def old(text: String): String =
    text.replaceAll("""\bRooms\.""", "Old.")
      .replace("import FrFlowGen.Old.Types", "import FrFlowGen.Rooms.Types")
      .replace("import FrFlowGen.Old.Boundaries", "import FrFlowGen.Rooms.Boundaries")
      .replaceAll("""(?m)^namespace (Rooms|Old)\b(.*)$""", "namespace Old$2\nopen Rooms")
      .replaceAll("""(?m)^end Rooms\b""", "end Old")
