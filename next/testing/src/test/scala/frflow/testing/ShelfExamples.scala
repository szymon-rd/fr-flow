package frflow.testing

import frflow.*
import frflow.testing.Shelf.*

/** The shelf's examples, as a project writes them: `sbt test` runs them through the examples' runner
  * (`ExamplesFramework`), beside the munit suites.
  */
class ShelfExamples extends FrFlowExamples(kb):
  example("a long book is picked, a short one left", minPages := BigInt(100)):
    picks(List(Book("Long", 300), Book("Short", 10)), 2) is List(Book("Long", 300))

  example("an empty shelf gives nothing", minPages := BigInt(1)):
    picks(Nil, 1) is Nil
