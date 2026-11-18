package fullshortener

import frflow.*
import Links.shortener

// The full shortener's model: four promises to whoever holds a link, two of them proven from what the members do;
// what the members do, proven of the class; and the decision the third promise rests on.

val linkLeadsUntilRemoved = Node.claim("A link leads to its URL until it is removed.")(
  forall((code: Term[Code], url: Term[Url], later: shortener.History) =>
    val link = shortener.resolve(code)
    ((link === some(url)) && later.never(shortener.remove(code))) implies (link.following(later) === some(url))))

val removedLinkStaysRemoved = Node.claim("A removed link never leads anywhere again.")(
  forall((code: Term[Code], later: shortener.History) =>
    shortener.resolve(code).following(shortener.remove(code)).following(later).isEmpty))

val shortenIsIdempotent = Node.claim("Shortening a URL again gives the same link and changes nothing.")(
  forall((url: Term[Url]) => shortener.shorten(url).isIdempotent))

val codesAreNeverReused = Node.design("A new code is a number above every code given and every code removed, " +
  "so no code is given twice.")("src/main/scala/fullshortener/RetiringLinks.scala")

val fullShortener: FrModel = FrModel("FullShortener")(
  // The promises.
  linkLeadsUntilRemoved,
  Links.shortenedCodeResolves,
  removedLinkStaysRemoved,
  shortenIsIdempotent,
  // What the members do: the parts a promise is proven from.
  Links.shortenKeepsExistingLinks.refines(linkLeadsUntilRemoved),
  Links.removeKeepsOtherCodes.refines(linkLeadsUntilRemoved, removedLinkStaysRemoved),
  Links.removedCodeLeadsNowhere.refines(removedLinkStaysRemoved),
  Links.removedCodeNotReissued.refines(removedLinkStaysRemoved),
  Links.shortenChangesOnlyItsCode.refines(removedLinkStaysRemoved),
  // The decision no proof covers.
  codesAreNeverReused.refines(removedLinkStaysRemoved),
  Links.shortener.define(lifted[RetiringLinks]))
