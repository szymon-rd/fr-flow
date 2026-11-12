package frflow.api.fixture

import frflow.*
import frflow.api.*

/** `Shelf`'s claims assembled here, apart from the file they are written in. */
object Assembled:
  val kb = FrModel("Assembled")(Shelf.Before.nonNegative, Shelf.Before.sameAbove)
    .defining(Shelf.d.defineTested(_ => n => n.abs))
