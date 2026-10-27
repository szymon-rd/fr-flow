package frflow.api

import frflow.*

/** `Shelf`'s claims assembled here, apart from the file they are written in. */
object Assembled:
  val kb = KnowledgeBase("Assembled")(Shelf.Before.nonNegative, Shelf.Before.sameAbove)
    .implementTested(Shelf.d)(_ => n => n.abs)
