package frflow.core.spec

import frflow.core.name.SourceText

/** An elaborated value with the Scala it was written as: what Lean reads (`value`) and what the developer decides
  * (`source`). Rewording the Scala without changing what it elaborates to changes the decision, not the Lean.
  */
final case class Written[+A](value: A, source: SourceText)
