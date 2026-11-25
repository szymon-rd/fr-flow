package links

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** A link shortener: it gives a URL a short code, tells where a code leads, and removes a code. */
trait Links extends Mutable:
  /** Gives the URL a code: the one that already leads to it, or a new one. */
  update def shorten(url: Url): Code
  /** The URL the code leads to, if any. */
  def resolve(code: Code): Option[Url]
  /** Removes the code: it leads nowhere after. */
  update def remove(code: Code): Unit

/** The claims on the shortener's three members, each said through them. `resolve` changes nothing, as its trait
  * says (it is not `update`); the claims say what `shorten` and `remove` do to where codes lead, and how the three
  * relate.
  */
object Links:
  val shortener = Declaration[Links]("the link shortener: the codes it has given and the URLs they lead to")

  // shorten, on its own

  val shortenIsIdempotent = Node.claim("Shortening a URL a second time gives the code it gave the first time and " +
      "changes nothing.")(
    forall((u: Term[Url]) => shortener.shorten(u).isIdempotent))

  // shorten and resolve

  val shortenedCodeResolves = Node.claim("The code a URL is given leads to that URL.")(
    forall((u: Term[Url]) => shortener.shorten(u).andThen(code => shortener.resolve(code)) === some(u)))

  val shortenKeepsExistingLinks = Node.claim("Shortening never changes where a code that leads somewhere leads.")(
    forall((u: Term[Url], c: Term[Code]) =>
      shortener.resolve(c).isDefined implies shortener.resolve(c).unchangedBy(shortener.shorten(u))))

  // remove and resolve: what removing does, exactly, and its two cases

  val removeChangesOnlyThatCode = Node.claim("Once a code is removed, every code leads where it led before, but " +
      "the removed one, which leads nowhere.")(
    forall((c: Term[Code], d: Term[Code]) =>
      shortener.resolve(d).following(shortener.remove(c)) ===
        when(d === c)(none[Url]).otherwise(shortener.resolve(d))))

  val removedCodeLeadsNowhere = Node.claim("A removed code leads nowhere.")(
    forall((c: Term[Code]) => shortener.resolve(c).following(shortener.remove(c)).isEmpty))

  val removeKeepsOtherCodes = Node.claim("Removing a code changes where no other code leads.")(
    forall((c: Term[Code], d: Term[Code]) =>
      (c =!= d) implies shortener.resolve(d).unchangedBy(shortener.remove(c))))

  // remove and shorten

  val removedCodeNotReissued = Node.claim("A code just removed is not given to the next URL shortened.")(
    forall((c: Term[Code], u: Term[Url]) => shortener.shorten(u).following(shortener.remove(c)) =!= c))

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
