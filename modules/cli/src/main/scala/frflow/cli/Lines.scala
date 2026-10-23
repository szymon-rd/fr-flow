package frflow.cli

import frflow.protocol.*

/** The pieces views are made of: a section, and a node in one line. */
object Lines:
  /** A titled section, its lines indented; nothing when it has none. */
  def section(title: String, body: List[String], st: Style): List[String] =
    if body.isEmpty then Nil else "" :: st.heading(title) :: body.map("  " + _)

  /** Prose wrapped to the width (less `indent`), its later lines indented by `hang`. */
  def para(text: String, st: Style, indent: Int = 2, hang: Int = 2): List[String] =
    st.width.fold(List(text)) { w =>
      st.wrap(text, w - indent - hang) match
        case first :: rest => first :: rest.map(" " * hang + _)
        case Nil => Nil
    }

  def state(r: Reviewed): String =
    if r.state == ReviewState.Review then s"review: ${r.review.causes.mkString(", ")}" else r.state.toString

  /** A node as one line: its status, id, kind, review state and statement, cut to the width (less `indent`). */
  def node(r: Reviewed, st: Style, indent: Int = 2, extra: String = ""): String =
    val head = s"${st.glyph(Glyph.of(r))} ${st.bold(r.id.value)}  ${st.dim(r.node.shownKind)}  ${st.state(r.state, state(r))}$extra  "
    val statement = r.node.content.statement.replaceAll("\\s+", " ").trim
    head + st.width.fold(statement)(w => st.cut(statement, (w - indent - Style.visible(head)).max(12)))
