package frflow.cli

import frflow.api.*

/** The DAG as lines: from the root with box-drawing characters, each node once under its first parent and
  * `⇢ X` under the others; then the assumptions and the other nodes under no parent, the definitions, the
  * gone nodes; the summary last. A row says the kind unless a claim and the state unless accepted; its
  * statement is cut to the width.
  */
object TreeText:
  def lines(t: Tree, st: Style): List[String] =
    def rows(n: TreeNode, prefix: String, cont: String): List[String] =
      val r = n.node
      val row = st.fit(s"$prefix${st.glyph(r)} ${st.bold(r.id.value)}${Lines.marks(r, st, n.withAgent)}  ${Lines.statement(r)}")
      val kids = n.children.map(Left(_)) ++ n.seeAlso.map(Right(_))
      row :: kids.zipWithIndex.flatMap { (k, i) =>
        val end = i == kids.size - 1
        val (p, c) = (cont + (if end then st.last else st.tee), cont + (if end then "   " else st.bar))
        k.fold(rows(_, p, c), id => List(st.dim(s"$p${st.see} $id")))
      }
    def section(title: String, ns: List[TreeNode]) =
      if ns.isEmpty then Nil else (if title.isEmpty then Nil else List("", st.heading(title))) ++ ns.flatMap(rows(_, "", ""))
    val gone = if t.gone.isEmpty then Nil
      else "" :: st.heading("Gone from the model: accept that each is gone (gone NODE)") ::
        t.gone.map(g => st.fit(s"${st.red(st.dot)} ${st.bold(g.id.value)}  ${st.dim(g.decision.content.statement)}"))
    (section("", t.main) ++ section("Assumptions, under no parent: trusted (the code calls them)", t.assumptions) ++
      section("Under no parent", t.unparented) ++ section("Definitions: they fix terms of the vocabulary (decided, not proven)", t.definitions))
      .dropWhile(_.isEmpty) ++ gone ++ ("" :: SummaryText.lines(t.overview, st))
