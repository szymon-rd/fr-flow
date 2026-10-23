package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** Something the theory says that mentions what was asked for. */
enum Mentioned derives Codec.AsObject:
  case Node(id: NodeId)
  case Rejected(id: NodeId, statement: String, reason: String)
  case Gone(id: NodeId)
  case NotModelled(line: String)
  case Idea(line: String)
  case Term(at: NodeId, meaning: String)

/** A mention, with its sentence that holds a word asked for. */
final case class Mention(what: Mentioned, sentence: Option[String]) derives Codec.AsObject

/** Where a change belongs. */
enum Found derives Codec.AsObject:
  /** The nodes governing a file (or a directory, or a file in a directory governed). */
  case Governed(path: String, nodes: List[NodeId])
  /** A source path no node governs: code there changes unnoticed. */
  case Ungoverned(path: String)
  /** A path that names no file or directory of the project (the API tells it from `Ungoverned`). */
  case Missing(path: String)
  /** What mentions every word asked for (at most ten). */
  case Mentions(query: String, mentions: List[Mention])
  case Nothing(query: String)

object Find:
  def apply(a: Annotated, query: String): Found =
    val q = query.stripPrefix("./")
    def governs(f: String) = f == q || f.startsWith(q.stripSuffix("/") + "/") || q.startsWith(f.stripSuffix("/") + "/")
    val governing = a.nodes.filter(_.node.code.exists(_.files.exists(governs))).map(_.id)
    if governing.nonEmpty then Found.Governed(q, governing)
    else if q.contains('/') || q.endsWith(".scala") then Found.Ungoverned(q)
    else
      // Every word of the query, anywhere in the entry, whatever the case.
      val words = query.toLowerCase.split("\\s+").filter(_.nonEmpty).toList
      def sentence(text: String) =
        text.split("(?<=[.!?])\\s+|\n").find(x => words.exists(x.toLowerCase.contains)).map(_.trim).filter(_.nonEmpty)
      val found = entries(a).filter((_, text) => words.forall(text.toLowerCase.contains)).take(10)
      if found.isEmpty then Found.Nothing(query) else Found.Mentions(query, found.map((m, text) => Mention(m, sentence(text))))

  private def entries(a: Annotated): List[(Mentioned, String)] =
    val ns = a.nodes
    def content(k: String) = ns.flatMap(_.node.content.str(k)).distinct
    def paragraphs(text: String, split: String) = text.split(split).map(_.trim).filter(_.nonEmpty).toList
    val nodes = ns.map(r => Mentioned.Node(r.id) -> (r.id.value :: List("statement", "why").flatMap(r.node.content.str) ++
      r.review.history.map(_.reason)).mkString(" \n"))
    val rejected = ns.flatMap(_.review.rejectedBeside).distinctBy(_.id).filterNot(r => a.byId.contains(r.id))
      .map(r => Mentioned.Rejected(r.id, r.statement, r.reason) -> s"${r.id} ${r.statement} \n${r.why} \n${r.reason}")
    val gone = a.gone.map(g => Mentioned.Gone(g.id) -> s"${g.id} ${g.decision.reason}")
    val notModelled = content("notModelled").flatMap(paragraphs(_, "\n(?=- )")).distinct.map(l => Mentioned.NotModelled(l) -> l)
    val idea = content("idea").flatMap(paragraphs(_, "\n\\s*\n")).filterNot(_.startsWith("#")).distinct.map(l => Mentioned.Idea(l) -> l)
    val terms = ns.flatMap(r => r.node.content.strs("vocabulary").map(r.id -> _)).distinctBy(_._2).map((id, v) => Mentioned.Term(id, v) -> v)
    nodes ++ rejected ++ gone ++ notModelled ++ idea ++ terms

/** IDEA.md as the decisions read it: what a root is decided against, by section, and what is not modelled. */
object Idea:
  /** The `## ` sections but Not modelled, by heading, after the lead (which every section-root is decided against too). */
  def sections(decided: String): (String, List[(String, String)]) =
    val (intro, rest) = decided.linesIterator.toList.span(l => !l.startsWith("## "))
    def go(ls: List[String]): List[(String, String)] = ls match
      case h :: tail =>
        val (body, more) = tail.span(l => !l.startsWith("## "))
        (h.stripPrefix("## ").trim -> (h :: body).mkString("\n").trim) :: go(more)
      case Nil => Nil
    (intro.mkString("\n").trim, go(rest))

  /** The idea a root is decided against, and its `## Not modelled` section. */
  def split(idea: String): (String, String) =
    val lines = idea.linesIterator.toList
    lines.indexWhere(_.trim.toLowerCase.startsWith("## not modelled")) match
      case -1 => (idea.trim, "")
      case i =>
        val (section, rest) = lines.drop(i + 1).span(l => !(l.startsWith("# ") || l.startsWith("## ")))
        ((lines.take(i) ++ rest).mkString("\n").trim, section.mkString("\n").trim)
