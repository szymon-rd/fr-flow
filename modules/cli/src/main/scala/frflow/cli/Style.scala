package frflow.cli

import frflow.protocol.{CheckStatus, ReviewState}

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
  def blue(s: String): String = ansi("34")(s)
  def magenta(s: String): String = ansi("35")(s)
  def cyan(s: String): String = ansi("36")(s)
  def heading(s: String): String = bold(s)

  private def pick(u: String, a: String) = if unicode then u else a
  def ellipsis: String = pick("…", "...")
  def bullet: String = pick("•", "-")
  def arrow: String = pick("→", "->")
  def follows: String = pick("↳", "->")
  def see: String = pick("⇢", "->")
  def dot: String = pick("·", "-")
  def rule: String = pick("───", "---")
  def tee: String = pick("├─ ", "|- ")
  def last: String = pick("└─ ", "`- ")
  def bar: String = pick("│  ", "|  ")

  /** A check status as one glyph, colored: ✓ proven, ○ open, ✗ failed, … waiting, ? unchecked, ≈ decided by reading. */
  def glyph(g: Glyph): String = g match
    case Glyph.Proven    => green(pick("✓", "+"))
    case Glyph.Open      => yellow(pick("○", "o"))
    case Glyph.Failed    => red(pick("✗", "x"))
    case Glyph.Waiting   => yellow(pick("…", "."))
    case Glyph.Unchecked => dim("?")
    case Glyph.Informal  => dim(pick("≈", "~"))
    case Glyph.None      => dim(pick("·", "-"))

  def state(s: ReviewState, text: String): String = s match
    case ReviewState.Accepted => green(text)
    case ReviewState.Proposed => cyan(text)
    case ReviewState.Review   => yellow(text)
    case ReviewState.Rejected => red(text)

  /** `s` cut to `room` visible characters, with an ellipsis. */
  def cut(s: String, room: Int): String =
    if s.length <= room then s else if room <= ellipsis.length then s.take(room.max(0)) else s.take(room - ellipsis.length).stripTrailing + ellipsis

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
  /** How wide `s` shows: without its ANSI codes. */
  def visible(s: String): Int = Ansi.replaceAllIn(s, "").length
  def strip(s: String): String = Ansi.replaceAllIn(s, "")

/** A node's check status as people scan it in a tree. */
enum Glyph:
  case Proven, Open, Failed, Waiting, Unchecked, Informal, None

object Glyph:
  import frflow.protocol.Reviewed
  /** Proven only when nothing of it is unproven; a definition or a design decision has no check. */
  def of(r: Reviewed): Glyph =
    val (ok, total) = r.node.examplesPassing
    r.node.status match
      case scala.None => Glyph.None
      case Some(CheckStatus.Failed | CheckStatus.ModelError) => Glyph.Failed
      case Some(_) if ok != total => Glyph.Failed
      case Some(CheckStatus.Open) => Glyph.Open
      case Some(CheckStatus.Waiting | CheckStatus.Timeout) => Glyph.Waiting
      case Some(CheckStatus.Unchecked) => Glyph.Unchecked
      case Some(CheckStatus.Informal) => Glyph.Informal
      case Some(CheckStatus.Proven) => if r.review.unproven.isEmpty then Glyph.Proven else Glyph.Open
