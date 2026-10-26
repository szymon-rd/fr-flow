package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** The DAG from the root, each node once under its first parent and `⇢ X` under the others; `c`, what layers on top add. */
object TreeText:
  def lines(t: Tree, st: Style, c: Contribution = Contribution.empty): List[String] =
    def rows(n: TreeNode, prefix: String, cont: String): List[String] =
      val r = n.node
      val head = s"$prefix${st.glyph(r)} ${st.bold(r.id.value)}${Lines.marks(r, st, c.marks.get(r.id))}  "
      val kids = n.children.map(Left(_)) ++ n.seeAlso.map(Right(_))
      // The root is read whole: wrapped at its clauses, under its statement, not cut.
      val row =
        if r.node.parents.isEmpty && prefix.isEmpty && (r.node.kind == NodeKind.Claim || kids.nonEmpty) then
          Lines.clauses(Lines.statement(r), st, Style.visible(head), if kids.isEmpty then "" else st.bar) match
            case first :: rest => (head + first) :: rest
            case Nil           => List(head)
        else List(st.fit(head + Lines.statement(r)))
      row ++ kids.zipWithIndex.flatMap { (k, i) =>
        val end = i == kids.size - 1
        val (p, c) = (cont + (if end then st.last else st.tee), cont + (if end then "   " else st.bar))
        k.fold(rows(_, p, c), id => List(st.dim(s"$p${st.see} $id")))
      }
    def section(title: String, ns: List[TreeNode]) =
      if ns.isEmpty then Nil else (if title.isEmpty then Nil else List("", st.bold(title))) ++ ns.flatMap(rows(_, "", ""))
    val gone = if t.gone.isEmpty then Nil
      else "" :: st.bold("Gone from the model: accept that each is gone (gone NODE)") ::
        t.gone.map(g => st.fit(s"${st.red(st.dot)} ${st.bold(g.id.value)}  ${st.dim(g.decision.content.statement)}"))
    (section("", t.main) ++ section("Assumptions, under no parent: trusted (the code calls them)", t.assumptions) ++
      section("Under no parent", t.unparented) ++ section("Definitions: they fix terms of the vocabulary (decided, not proven)", t.definitions))
      .dropWhile(_.isEmpty) ++ gone ++ ("" :: SummaryText.lines(t.overview, st, c.waiting(st)))
