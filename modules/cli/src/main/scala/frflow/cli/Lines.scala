package frflow.cli

import frflow.protocol.*

/** The pieces views are made of: a section, wrapped prose, and a node in one line. */
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

  /** What sets a node apart in a list: its kind unless a claim, its review state unless accepted. */
  def marks(r: Reviewed, st: Style, asked: Boolean = false): String =
    val kind = Option.when(r.node.shownKind != "claim")(st.dim(r.node.shownKind))
    val review = Option.when(r.state != ReviewState.Accepted)(st.state(r.state, state(r)))
    (kind.toList ++ review ++ Option.when(asked)(st.magenta("asked"))).map("  " + _).mkString

  def statement(r: Reviewed): String = r.node.content.statement.replaceAll("\\s+", " ").trim

  /** A node as one line: its status, id, kind and review state when they say something, and its statement,
    * cut to the width (less `indent`).
    */
  def node(r: Reviewed, st: Style, indent: Int = 2, extra: String = ""): String =
    st.fit(s"${st.glyph(r)} ${st.bold(r.id.value)}${marks(r, st)}$extra  ${statement(r)}", indent)
