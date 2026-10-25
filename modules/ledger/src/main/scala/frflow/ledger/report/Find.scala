package frflow
package ledger
package report

import frflow.protocol.*

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
