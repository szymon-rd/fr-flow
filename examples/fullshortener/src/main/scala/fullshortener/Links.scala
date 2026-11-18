package fullshortener

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

/** What each member does, said through the members: the parts the shortener's promises are proven from, each
  * proven of the class. `resolve` changes nothing, as its trait says (it is not `update`).
  */
object Links:
  val shortener = Declaration[Links]("the link shortener: the codes it has given and the URLs they lead to")

  // shorten

  val shortenedCodeResolves = Node.claim("The code a URL is given leads to that URL.")(
    forall((url: Term[Url]) => shortener.shorten(url).andThen(code => shortener.resolve(code)) === some(url)))

  val shortenKeepsExistingLinks = Node.claim("Shortening a URL never changes where an existing code leads.")(
    forall((url: Term[Url], code: Term[Code]) =>
      shortener.resolve(code).isDefined implies shortener.resolve(code).unchangedBy(shortener.shorten(url))))

  val shortenChangesOnlyItsCode = Node.claim("Shortening a URL changes where no code leads but the one it gives.")(
    forall((url: Term[Url], other: Term[Code]) =>
      (other =!= shortener.shorten(url).result) implies
        shortener.resolve(other).unchangedBy(shortener.shorten(url))))

  // remove

  val removedCodeLeadsNowhere = Node.claim("A removed code leads nowhere.")(
    forall((code: Term[Code]) => shortener.resolve(code).following(shortener.remove(code)).isEmpty))

  val removeKeepsOtherCodes = Node.claim("Removing a code never changes where any other code leads.")(
    forall((code: Term[Code], other: Term[Code]) =>
      (code =!= other) implies shortener.resolve(other).unchangedBy(shortener.remove(code))))

  val removedCodeNotReissued = Node.claim("A removed code is never given to a URL again.")(
    forall((code: Term[Code], url: Term[Url], later: shortener.History) =>
      shortener.shorten(url).following(shortener.remove(code)).following(later) =!= code))
