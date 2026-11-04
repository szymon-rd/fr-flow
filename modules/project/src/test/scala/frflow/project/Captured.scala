package frflow.project

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** What today's library recorded of an example (`reference/<name>`): each node's standing, where it sits and what it
  * assumes as `show` printed them, and its generated Lean, which a port puts in namespace `Old` to state its claims
  * equivalent to today's.
  */
final class Captured(name: String):
  val dir: Path = Path.of("reference", name)

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

  /** Today's Lean of the example (`FrFlowGen/<Kb>`), each file by its path under it, the domain's and each node's
    * `Spec` only.
    */
  def specs(kb: String): List[(String, String)] =
    val root = dir.resolve(s"lean/FrFlowGen/$kb")
    Files.walk(root).iterator.asScala.toList.filter(Files.isRegularFile(_)).map(p => root.relativize(p).toString)
      .filter(r => r.startsWith("Domain") || r == "Types.lean" || r.endsWith("/Spec.lean")).sorted
      .map(r => r -> Files.readString(root.resolve(r)))

  /** Today's Lean in namespace `Old`, under `FrFlowGen/Old`, over the port's types (`FrFlowGen.<Kb>.Types`, opened):
    * by path under `lean/`, `rename` applied to each file's text once moved.
    */
  def old(kb: String, rename: String => String): List[(String, String)] =
    specs(kb).filterNot(_._1 == "Types.lean").map((p, text) => s"FrFlowGen/Old/$p" -> rename(
      text.replaceAll(s"""\\b$kb\\.""", "Old.")
        .replace("import FrFlowGen.Old.Types", s"import FrFlowGen.$kb.Types")
        .replaceAll(s"""(?m)^namespace ($kb|Old)\\b(.*)$$""", s"namespace Old$$2\nopen $kb")
        .replaceAll(s"""(?m)^end $kb\\b""", "end Old")))
