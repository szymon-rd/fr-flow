package frflow.cli
package text

import frflow.protocol.{Content, ReviewState, Reviewed}

/** The pieces views are made of: a section, wrapped prose, and a node in one line. */
object Lines:
  /** Nothing when it has no lines. */
  def section(title: String, body: List[String], st: Style): List[String] =
    if body.isEmpty then Nil else "" :: st.bold(title) :: body.map("  " + _)

  /** Wrapped to the width (less `indent`), its later lines indented by `hang`. */
  def para(text: String, st: Style, indent: Int = 2, hang: Int = 2): List[String] =
    st.width.fold(List(text)) { w =>
      st.wrap(text, w - indent - hang) match
        case first :: rest => first :: rest.map(" " * hang + _)
        case Nil => Nil
    }

  /** The node's reason, dimmed and indented; nothing when it gives none. */
  def why(c: Content, room: Int, st: Style): List[String] =
    if c.why.trim.isEmpty then Nil else st.wrap(s"why: ${c.why}", room).map(l => "  " + st.dim(l))

  def state(r: Reviewed): String =
    if r.state == ReviewState.Review then s"to review: ${r.review.causes.map(Words.cause).mkString(", ")}" else r.state.toString

  /** Its kind unless a claim, its review state unless accepted, and the word a layer on top shows beside it (`mark`). */
  def marks(r: Reviewed, st: Style, mark: Option[String] = None): String =
    val kind = Option.when(r.node.shownKind != "claim")(st.dim(r.node.shownKind))
    val review = Option.when(r.state != ReviewState.Accepted)(st.state(r.state, state(r)))
    (kind.toList ++ review ++ mark.map(st.magenta)).map("  " + _).mkString

  def statement(r: Reviewed): String = r.node.content.statement.replaceAll("\\s+", " ").trim

  /** A statement after `indent` characters, whole: on one line when it fits the width, else a clause a line (cut after
    * each ";" and before each ", and"), a clause longer than a line wrapped at its words; the later lines start with
    * `bar` and are indented under the first's text.
    */
  def clauses(text: String, st: Style, indent: Int, bar: String = ""): List[String] =
    st.width.filter(w => indent + Style.visible(text) > w).fold(List(text)) { w =>
      val room = (w - indent).max(20)
      val lines = text.split("(?<=;) +|(?<=,) +(?=and )").toList.flatMap(c => if c.length <= room then List(c) else st.wrap(c, room))
      lines.headOption.toList ++ lines.drop(1).map(l => bar + " " * (indent - Style.visible(bar)).max(0) + l)
    }

  /** Its status, id, marks and statement, cut to the width (less `indent`). */
  def node(r: Reviewed, st: Style, indent: Int = 2, extra: String = ""): String =
    st.fit(s"${st.glyph(r)} ${st.bold(r.id.value)}${marks(r, st)}$extra  ${statement(r)}", indent)
