package frflow
package lean
package obligation

import frflow.protocol.ObligationName

/** An example evaluated in Lean: `claim` is what Scala computes; Lean proving `opposite` means the translation is wrong. */
final case class Eval(name: ObligationName, what: String, claim: String, opposite: String, defs: List[Def[?]] = Nil)
