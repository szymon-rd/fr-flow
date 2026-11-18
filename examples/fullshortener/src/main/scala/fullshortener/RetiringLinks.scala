package fullshortener

import language.experimental.captureChecking
import language.experimental.separationChecking

/** What the shortener's class reads of the links it keeps. */
object Issued:
  /** Where the code leads: the URL of the first link with that code, if there is one. */
  def leadsTo(issued: List[Link], code: Code): Option[Url] = issued.find(l => l.code == code).map(l => l.url)

  /** A number above every code given and every code removed. */
  def above(issued: List[Link], retired: List[Code]): BigInt =
    (issued.map(l => l.code) ++ retired).foldLeft(BigInt(0))((top, c) =>
      if c.number >= top then c.number + BigInt(1) else top)

/** The shortener that keeps every link it gives, newest first, and every code removed. A URL that a code already
  * leads to is given that code; any other URL is given a number above every code given or removed, so a removed
  * code is never given again.
  */
final class RetiringLinks(var issued: List[Link], var retired: List[Code]) extends Links:
  update def shorten(url: Url): Code =
    val held = issued
    val known = held.find(l => Issued.leadsTo(held, l.code) == Some(url)).map(l => l.code)
    val code = known.getOrElse(Code(Issued.above(held, retired)))
    if known.isEmpty then issued = Link(code, url) :: held
    code

  def resolve(code: Code): Option[Url] = Issued.leadsTo(issued, code)

  update def remove(code: Code): Unit =
    issued = issued.filter(l => l.code != code)
    retired = code :: retired
