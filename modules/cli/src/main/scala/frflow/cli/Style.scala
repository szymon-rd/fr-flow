package frflow.cli

import frflow.protocol.{CheckStatus, ReviewState, Reviewed}

/** How text looks: ANSI colors and Unicode on a terminal, plain ASCII otherwise; and how wide a line may
  * be (none: as long as it is, for agents and files). Rendering builds plain strings through it.
  */
final case class Style(color: Boolean, unicode: Boolean, width: Option[Int]):
  private def ansi(code: String)(s: String) = if color && s.nonEmpty then s"\u001b[${code}m$s\u001b[0m" else s
  def bold(s: String): String = ansi("1")(s)
  def dim(s: String): String = ansi("2")(s)
  def red(s: String): String = ansi("31")(s)
  def green(s: String): String = ansi("32")(s)
  def yellow(s: String): String = ansi("33")(s)
  def magenta(s: String): String = ansi("35")(s)
  def cyan(s: String): String = ansi("36")(s)
  def heading(s: String): String = bold(s)

  private def pick(u: String, a: String) = if unicode then u else a
  def ellipsis: String = pick("…", "...")
  def bullet: String = pick("•", "-")
  def follows: String = pick("↳", "->")
  def see: String = pick("⇢", "->")
  def dot: String = pick("·", "-")
  def rule: String = pick("───", "---")
  def tee: String = pick("├─ ", "|- ")
  def last: String = pick("└─ ", "`- ")
  def bar: String = pick("│  ", "|  ")

  def proven: String = green(pick("✓", "+"))
  def open: String = yellow(pick("○", "o"))
  def failed: String = red(pick("✗", "x"))

  /** A node's check status as one glyph: ✓ proven (nothing of it unproven), ○ open, ✗ failed (or an example
    * failing), … waiting, ? unchecked; · no check (a definition, a design decision).
    */
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

  /** `s` cut to the width, less `indent`; as it is without a width. */
  def fit(s: String, indent: Int = 0): String = width.fold(s)(w => cut(s, (w - indent).max(12)))

  /** `s` in lines of at most `room` characters, broken between words. */
  def wrap(s: String, room: Int): List[String] =
    if room <= 0 then List(s)
    else s.split("\\s+").filter(_.nonEmpty).foldLeft(List.empty[String]) {
      case (Nil, w) => List(w)
      case (l :: done, w) if Style.visible(l) + 1 + Style.visible(w) <= room => s"$l $w" :: done
      case (done, w) => w :: done
    }.reverse

object Style:
  val plain: Style = Style(color = false, unicode = false, width = None)
  private val Ansi = "\u001b\\[[0-9;]*m".r
  private val Token = "(?s)\u001b\\[[0-9;]*m|.".r
  /** How wide `s` shows: without its ANSI codes. */
  def visible(s: String): Int = Ansi.replaceAllIn(s, "").length
  def strip(s: String): String = Ansi.replaceAllIn(s, "")
