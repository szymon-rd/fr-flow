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

/** The shortener's word: what the claims are said of, through its members (`FullShortener.scala`). `resolve` changes
  * nothing, as its trait says (it is not `update`).
  */
object Links:
  val shortener = Declaration[Links]("the link shortener: the codes it has given and the URLs they lead to")
