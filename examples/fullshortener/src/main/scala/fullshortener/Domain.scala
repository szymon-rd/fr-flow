package fullshortener

import frflow.*

// The shortener's words, before anything that uses them: a URL, the code it is given, and a link between them.

/** An address a code leads to. */
final case class Url(address: String) derives FrSpec

/** A short code: what a shortened link carries in place of its URL. */
final case class Code(number: BigInt) derives FrSpec

/** A code given to a URL. */
final case class Link(code: Code, url: Url) derives FrSpec
