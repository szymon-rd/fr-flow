package frflow.api

import frflow.protocol.*

/** Where a change belongs: the nodes governing a path, or what mentions every word asked for (a node's
  * id, statement, why or reasons; the options rejected; the gone nodes; Not modelled; the idea; the terms).
  */
object Find:
  def apply(v: View, query: String): Found =
    val q = query.trim.stripPrefix("./")
    def files(r: Reviewed) = r.node.code.fold(Nil)(_.files)
    def under(a: String, b: String) = a == b || a.startsWith(b.stripSuffix("/") + "/")
    val governing = v.nodes.filter(r => files(r).exists(f => under(f, q) || under(q, f)))
    if governing.nonEmpty then Found.Governed(q, governing)
    else if q.contains('/') || q.endsWith(".scala") then Found.Ungoverned(q)
    else Found.Mentions(query, mentions(v, query))

  private final case class Entry(kind: HitKind, id: Option[NodeId], label: String, text: String)

  private def entries(v: View): List[Entry] =
    val ns = v.nodes
    def content(k: String) = ns.flatMap(_.node.content.str(k)).distinct
    def flat(s: String) = s.replaceAll("\\s+", " ").trim
    val nodes = ns.map(r => Entry(HitKind.Node, Some(r.id), r.node.content.statement,
      (r.id.value :: List("statement", "why").flatMap(r.node.content.str) ++ r.review.history.map(_.reason)).mkString(" \n")))
    val rejected = ns.flatMap(_.review.rejectedBeside).distinctBy(_.id).filterNot(x => v.node(x.id).isDefined)
      .map(x => Entry(HitKind.Rejected, Some(x.id), s"${x.statement} — rejected because: ${x.reason}", s"${x.id} ${x.statement} \n${x.why} \n${x.reason}"))
    val gone = v.annotated.gone.map(g => Entry(HitKind.Gone, Some(g.id), g.decision.content.statement, s"${g.id} ${g.decision.reason}"))
    val notModelled = content("notModelled").flatMap(_.split("\n(?=- )").map(_.trim).filter(_.nonEmpty)).distinct
      .map(l => Entry(HitKind.NotModelled, None, flat(l), l))
    val idea = content("idea").flatMap(_.split("\n\\s*\n").map(_.trim).filter(l => l.nonEmpty && !l.startsWith("#"))).distinct
      .map(l => Entry(HitKind.Idea, None, flat(l).take(160), l))
    val terms = ns.flatMap(r => r.node.content.strs("vocabulary").map(r.id -> _)).distinctBy(_._2)
      .map((id, t) => Entry(HitKind.Term, Some(id), t, t))
    nodes ++ rejected ++ gone ++ notModelled ++ idea ++ terms

  /** Every word of the query, anywhere in the entry, whatever the case; the first ten, each with the
    * sentence that mentions it when the label does not.
    */
  private def mentions(v: View, query: String): List[Hit] =
    val words = query.toLowerCase.split("\\s+").filter(_.nonEmpty).toList
    def sentence(e: Entry) = e.text.split("(?<=[.!?])\\s+|\n").map(_.trim)
      .find(x => x.nonEmpty && !e.id.exists(_.value == x) && words.exists(x.toLowerCase.contains)).filterNot(e.label.contains).map(_.take(200))
    entries(v).filter(e => words.forall(e.text.toLowerCase.contains)).take(10).map(e => Hit(e.kind, e.id, e.label, sentence(e)))
