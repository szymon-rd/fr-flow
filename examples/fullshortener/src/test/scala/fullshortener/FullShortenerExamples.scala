package fullshortener

import frflow.*
import Links.shortener

/** The shortener at work: code 0 leads home. */
class FullShortenerExamples extends FrFlowExamples(fullShortener):
  private val (home, docs) = (Url("https://example.com"), Url("https://example.com/docs"))
  private val one = shortener.holding(RetiringLinks(List(Link(Code(0), home)), Nil))

  example("a new URL: a new code, which leads to it, and code 0 still leads home"):
    val asked = shortener.shorten(docs).in(one)
    (asked.result is Code(1)) && (shortener.resolve(Code(1)).following(asked) is Some(docs)) &&
      (shortener.resolve(Code(0)).following(asked) is Some(home))

  example("a URL shortened again: its code, and nothing changed"):
    val asked = shortener.shorten(home).in(one)
    (asked.result is Code(0)) && asked.changesNothing

  example("a removed code: it leads nowhere, and is not given again"):
    val removed = shortener.remove(Code(0)).in(one)
    (shortener.resolve(Code(0)).following(removed) is None) &&
      (shortener.shorten(home).following(removed).result is Code(1))
