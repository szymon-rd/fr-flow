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

  /** ✓ proven (nothing of it unproven), ○ open, ✗ failed (or an example failing), … waiting, ? unchecked, · no check;
    * ! a node the developer is to decide (new, or back for review), unless it fails: its proof is not what to look at.
    */
  def glyph(r: Reviewed): String =
    val (ok, total) = r.node.examplesPassing
    val decide = r.state == ReviewState.Review || r.state == ReviewState.Proposed
    val fails = r.node.status match
      case Some(CheckStatus.Failed | CheckStatus.ModelError) => true
      case None                                             => r.node.tested.exists(_.failure.isDefined)
      case Some(_)                                          => ok != total
    r.node.status match
      case _ if fails => failed
      case _ if decide => yellow("!")
      case None | Some(CheckStatus.Failed | CheckStatus.ModelError) => dim(pick("·", "-"))
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
      kept.mkString.stripTrailing + ellipsis + (if color then Style.Reset else "")

  def fit(s: String, indent: Int = 0): String = width.fold(s)(w => cut(s, (w - indent).max(12)))

  /** `s` wrapped to the width (less `indent`), its later lines indented under its text: nothing is cut.
    * For source and diff lines; their spaces are kept, and a word longer than a line is split.
    */
  def fold(s: String, indent: Int = 0): List[String] = width.map(w => (w - indent).max(20)).filter(Style.visible(s) > _).fold(List(s)) { room =>
    val hang = " " * (Style.strip(s).takeWhile(_ == ' ').length + 2).min(room / 2)
    val pieces = Style.Piece.findAllIn(s).toList.flatMap(p => if p.startsWith("\u001b") then List(p) else p.grouped(room - hang.length).toList)
    // The colors open at a break are closed, and opened again on the next line.
    val (done, last, _) = pieces.foldLeft((Vector.empty[String], "", Vector.empty[String])) { case ((done, line, codes), p) =>
      if p.startsWith("\u001b") then (done, line + p, if p == Style.Reset then Vector.empty else codes :+ p)
      else if Style.visible(line) + p.length <= room then (done, line + p, codes)
      else (done :+ (line.stripTrailing + (if codes.isEmpty then "" else Style.Reset)), hang + codes.mkString + (if p.isBlank then "" else p), codes)
    }
    (done :+ last).toList
  }
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
  private val Piece = "\u001b\\[[0-9;]*m|\\s+|[^\\s\u001b]+".r
  private val Reset = "\u001b[0m"

  /** Colors and Unicode on a terminal, unless `--plain`, `NO_COLOR` or `TERM=dumb`; lines cut (or wrapped) to
    * `COLUMNS`, which bin/frflow sets, only on a terminal: CI, agents and files read every line whole.
    */
  def of(plain: Boolean, env: Map[String, String], terminal: Boolean): Style =
    val color = !plain && terminal && !env.contains("NO_COLOR") && !env.get("TERM").contains("dumb")
    Style(color, unicode = color, env.get("COLUMNS").flatMap(_.toIntOption).filter(_ > 20 && terminal))
  def visible(s: String): Int = strip(s).length
  def strip(s: String): String = Ansi.replaceAllIn(s, "")
