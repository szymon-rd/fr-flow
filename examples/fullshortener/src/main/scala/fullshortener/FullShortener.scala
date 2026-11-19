package fullshortener

import frflow.*
import Links.shortener

// The full shortener's model: four promises to whoever holds a link; below them what the members do, each placed
// under the promise it helps prove and proven of the class; and the decision the third promise rests on.

// The promises.

val linkLeadsUntilRemoved = Node.claim("A link leads to its URL until it is removed.")(
  forall((code: Term[Code], url: Term[Url], later: shortener.History) =>
    val link = shortener.resolve(code)
    ((link === some(url)) && later.never(shortener.remove(code))) implies (link.following(later) === some(url))))

val shortenedCodeResolves = Node.claim("The code a URL is given leads to that URL.")(
  forall((url: Term[Url]) => shortener.shorten(url).andThen(code => shortener.resolve(code)) === some(url)))

val removedLinkStaysRemoved = Node.claim("A removed link never leads anywhere again.")(
  forall((code: Term[Code], later: shortener.History) =>
    val removal = shortener.remove(code)
    val whereItLeads = shortener.resolve(code).following(removal).following(later)
    whereItLeads.isEmpty))

val shortenIsIdempotent = Node.claim("Shortening a URL again gives the same link and changes nothing.")(
  forall((url: Term[Url]) => shortener.shorten(url).isIdempotent))

// What shortening does.

val shortenKeepsExistingLinks = Node.claim("Shortening a URL never changes where an existing code leads.")(
  forall((url: Term[Url], code: Term[Code]) =>
    shortener.resolve(code).isDefined implies shortener.resolve(code).unchangedBy(shortener.shorten(url))))
  .refines(linkLeadsUntilRemoved)

val shortenChangesOnlyItsCode = Node.claim("Shortening a URL changes where no code leads but the one it gives.")(
  forall((url: Term[Url], other: Term[Code]) =>
    (other =!= shortener.shorten(url).result) implies
      shortener.resolve(other).unchangedBy(shortener.shorten(url))))
  .refines(removedLinkStaysRemoved)

// What removing does.

val removedCodeLeadsNowhere = Node.claim("A removed code leads nowhere.")(
  forall((code: Term[Code]) => shortener.resolve(code).following(shortener.remove(code)).isEmpty))
  .refines(removedLinkStaysRemoved)

val removeKeepsOtherCodes = Node.claim("Removing a code never changes where any other code leads.")(
  forall((code: Term[Code], other: Term[Code]) =>
    (code =!= other) implies shortener.resolve(other).unchangedBy(shortener.remove(code))))
  .refines(linkLeadsUntilRemoved, removedLinkStaysRemoved)

val removedCodeNotReissued = Node.claim("A removed code is never given to a URL again.")(
  forall((code: Term[Code], url: Term[Url], later: shortener.History) =>
    shortener.shorten(url).following(shortener.remove(code)).following(later) =!= code))
  .refines(removedLinkStaysRemoved)

// The decision no proof covers.

val codesAreNeverReused = Node.design("A new code is a number above every code given and every code removed, " +
  "so no code is given twice.")("src/main/scala/fullshortener/RetiringLinks.scala")
  .refines(removedLinkStaysRemoved)

val fullShortener: FrModel = FrModel("FullShortener")(
  linkLeadsUntilRemoved, shortenedCodeResolves, removedLinkStaysRemoved, shortenIsIdempotent,
  shortenKeepsExistingLinks, shortenChangesOnlyItsCode,
  removedCodeLeadsNowhere, removeKeepsOtherCodes, removedCodeNotReissued,
  codesAreNeverReused,
  shortener.define(lifted[RetiringLinks]))
