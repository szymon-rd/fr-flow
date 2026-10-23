package frflow.cli

import frflow.protocol.{CheckStatus, ReviewState, Reviewed}

/** ANSI colors and Unicode on a terminal, plain ASCII otherwise; `width` none: lines as long as they are. */
final case class Style(color: Boolean, unicode: Boolean, width: Option[Int]):
  private def ansi(code: String)(s: String) = if color && s.nonEmpty then s"\u001b[${code}m$s\u001b[0m" else s
  def bold(s: String): String = ansi("1")(s)
  def dim(s: String): String = ansi("2")(s)
  def red(s: String): String = ansi("31")(s)
  def green(s: String): String = ansi("32")(s)
  def yellow(s: String): String = ansi("33")(s)
  def magenta(s: String): String = ansi("35")(s)
  def cyan(s: String): String = ansi("36")(s)

  private def pick(u: String, a: String) = if unicode then u else a
  val (ellipsis, bullet, follows, see, dot, rule, tee, last, bar) =
    if unicode then ("…", "•", "↳", "⇢", "·", "───", "├─ ", "└─ ", "│  ") else ("...", "-", "->", "->", "-", "---", "|- ", "`- ", "|  ")
  def proven: String = green(pick("✓", "+"))
  def open: String = yellow(pick("○", "o"))
  def failed: String = red(pick("✗", "x"))

  /** ✓ proven (nothing of it unproven), ○ open, ✗ failed (or an example failing), … waiting, ? unchecked, · no check. */
  def glyph(r: Reviewed): String =
    val (ok, total) = r.node.examplesPassing
    r.node.status match
      case None => dim(pick("·", "-"))
      case Some(CheckStatus.Failed | CheckStatus.ModelError) => failed
      case Some(_) if ok != total => failed
      case Some(CheckStatus.Open) => open
      case Some(CheckStatus.Waiting | CheckStatus.Timeout) => yellow(pick("…", "."))
      case Some(CheckStatus.Unchecked) => dim("?")
      case Some(CheckStatus.Proven) => if r.review.unproven.isEmpty then proven else open

  def state(s: ReviewState, text: String): String = s match
    case ReviewState.Accepted => green(text)
    case ReviewState.Proposed => cyan(text)
    case ReviewState.Review   => yellow(text)
    case ReviewState.Rejected => red(text)

  /** `s` cut to `room` visible characters, with an ellipsis; its colors kept. */
  def cut(s: String, room: Int): String =
    if Style.visible(s) <= room then s
    else
      val keep = (room - ellipsis.length).max(0)
      val (kept, _) = Style.Token.findAllIn(s).foldLeft((Vector.empty[String], 0)) { case ((out, n), t) =>
        if t.startsWith("\u001b") then (out :+ t, n) else if n < keep then (out :+ t, n + 1) else (out, n)
      }
      kept.mkString.stripTrailing + ellipsis + (if color then "\u001b[0m" else "")

  def fit(s: String, indent: Int = 0): String = width.fold(s)(w => cut(s, (w - indent).max(12)))
  def wrap(s: String, room: Int): List[String] =
    if room <= 0 then List(s)
    else s.split("\\s+").filter(_.nonEmpty).foldLeft(List.empty[String]) {
      case (Nil, w) => List(w)
      case (l :: done, w) if Style.visible(l) + 1 + Style.visible(w) <= room => s"$l $w" :: done
      case (done, w) => w :: done
    }.reverse

object Style:
  private val Ansi = "\u001b\\[[0-9;]*m".r
  private val Token = "(?s)\u001b\\[[0-9;]*m|.".r
  def visible(s: String): Int = strip(s).length
  def strip(s: String): String = Ansi.replaceAllIn(s, "")

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

  def state(r: Reviewed): String =
    if r.state == ReviewState.Review then s"review: ${r.review.causes.mkString(", ")}" else r.state.toString

  /** Its kind unless a claim, its review state unless accepted. */
  def marks(r: Reviewed, st: Style, asked: Boolean = false): String =
    val kind = Option.when(r.node.shownKind != "claim")(st.dim(r.node.shownKind))
    val review = Option.when(r.state != ReviewState.Accepted)(st.state(r.state, state(r)))
    (kind.toList ++ review ++ Option.when(asked)(st.magenta("asked"))).map("  " + _).mkString

  def statement(r: Reviewed): String = r.node.content.statement.replaceAll("\\s+", " ").trim

  /** Its status, id, marks and statement, cut to the width (less `indent`). */
  def node(r: Reviewed, st: Style, indent: Int = 2, extra: String = ""): String =
    st.fit(s"${st.glyph(r)} ${st.bold(r.id.value)}${marks(r, st)}$extra  ${statement(r)}", indent)
