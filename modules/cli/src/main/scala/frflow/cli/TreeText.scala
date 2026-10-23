package frflow.cli

import frflow.api.*
import frflow.protocol.*

/** The DAG as lines: from the root with box-drawing characters, each node once under its first parent
  * and a reference to it under the others; then the assumptions and the other nodes under no parent, the
  * definitions, the gone nodes; the summary last. Columns line up; statements are cut to the width (or,
  * `full`, wrapped under it).
  */
object TreeText:
  private enum Item:
    case Node(t: TreeNode)
    case Ref(id: NodeId, drawnUnder: Option[NodeId])

  private final case class Row(prefix: String, cont: String, item: Item)

  private val KindWidth = 11
  private val MaxIdColumn = 46
  private val MaxStateWidth = 24

  def lines(t: Tree, st: Style, full: Boolean = false): List[String] =
    val index = all(t).map(n => n.node.id -> n).toMap
    def drawnUnder(id: NodeId) = index.get(id).flatMap(_.node.node.parents.find(index.contains))
    def rows(n: TreeNode, prefix: String, cont: String): List[Row] =
      val kids = n.children.map(Left(_)) ++ n.seeAlso.map(Right(_))
      Row(prefix, cont, Item.Node(n)) :: kids.zipWithIndex.flatMap { (k, i) =>
        val end = i == kids.size - 1
        val (p, c) = (cont + (if end then st.last else st.tee), cont + (if end then "   " else st.bar))
        k.fold(rows(_, p, c), id => List(Row(p, c, Item.Ref(id, drawnUnder(id)))))
      }
    def section(title: String, ns: List[TreeNode]) = (title, ns.flatMap(rows(_, "", "")))
    val sections = List(section("", t.main), section("Assumptions, under no parent: trusted (the code calls them)", t.assumptions),
      section("Under no parent", t.unparented), section("Definitions: they fix terms of the vocabulary (decided, not proven)", t.definitions))
      .filter(_._2.nonEmpty)
    val allRows = sections.flatMap(_._2)
    val idColumn = allRows.collect { case r @ Row(_, _, Item.Node(n)) => r.prefix.length + 2 + n.node.id.value.length }.maxOption.getOrElse(0).min(MaxIdColumn)
    val stateWidth = allRows.collect { case Row(_, _, Item.Node(n)) => stateText(n).length }.maxOption.getOrElse(0).min(MaxStateWidth)
    def render(r: Row): List[String] = r.item match
      case Item.Ref(id, under) => List(st.dim(s"${r.prefix}${st.see} $id${under.fold("")(u => s"  (drawn under $u)")}"))
      case Item.Node(n) => node(r, n, idColumn, stateWidth, st, full)
    val body = sections.zipWithIndex.flatMap { case ((title, rs), i) =>
      (if i == 0 && title.isEmpty then Nil else List("", st.heading(title))) ++ rs.flatMap(render)
    }
    val gone = if t.gone.isEmpty then Nil
      else "" :: st.heading("Gone from the model: accept that each is gone (gone NODE)") ::
        t.gone.map(g => s"${st.red(st.dot)} ${st.bold(g.id.value)}  ${st.dim(g.decision.content.statement)}")
    body ++ gone ++ ("" :: SummaryText.lines(t.overview, st))

  private def all(t: Tree): List[TreeNode] =
    def go(n: TreeNode): List[TreeNode] = n :: n.children.flatMap(go)
    (t.main ++ t.assumptions ++ t.unparented ++ t.definitions).flatMap(go)

  /** The review state as a word: `review` with its causes, `asked` while the agent has it. */
  def stateText(n: TreeNode): String =
    val r = n.node.review
    val base = if r.state == ReviewState.Review then s"review: ${r.causes.mkString(", ")}" else r.state.toString
    base + (if n.withAgent then " (asked)" else "")

  private def node(r: Row, n: TreeNode, idColumn: Int, stateWidth: Int, st: Style, full: Boolean): List[String] =
    val rv = n.node
    val left = s"${r.prefix}${st.glyph(Glyph.of(rv))} ${st.bold(rv.id.value)}"
    val pad = " " * ((idColumn - Style.visible(left)).max(0) + 2)
    val kind = rv.node.shownKind.padTo(KindWidth, ' ')
    val state = stateText(n)
    val head = s"$left$pad${st.dim(kind)} ${st.state(rv.state, state)}${" " * (stateWidth - state.length).max(0)}  "
    val statement = rv.node.content.statement.replaceAll("\\s+", " ").trim
    // Under this node, continuation lines keep its children's bar.
    val indent = r.cont + (if n.children.nonEmpty || n.seeAlso.nonEmpty then st.bar else "   ")
    val alsoText = if n.alsoUnder.isEmpty then "" else s"(also under ${n.alsoUnder.mkString(", ")})"
    // Too little room left for the statement: "also under" goes on a line of its own.
    val apart = alsoText.nonEmpty && st.width.exists(w => w - Style.visible(head) - alsoText.length < 40)
    val also = if alsoText.isEmpty || apart then "" else s"  $alsoText"
    val room = st.width.map(_ - Style.visible(head) - also.length)
    val main = (st.width, room) match
      case (Some(w), Some(k)) if full && k > 20 && statement.length > k =>
        st.wrap(statement, w - Style.visible(head)) match
          case first :: rest => (head + first + st.dim(also)) :: rest.map(l => st.dim(indent) + " " * (Style.visible(head) - indent.length).max(0) + l)
          case Nil => List(head + st.dim(also))
      case (_, Some(k)) if !full => List(head + st.cut(statement, k.max(12)) + st.dim(also))
      case _ => List(head + statement + st.dim(also))
    main ++ Option.when(apart)(st.dim(indent + " " * (Style.visible(head) - indent.length).max(0) + alsoText))
