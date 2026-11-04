package frflow.core.analysis

import frflow.core.{Elaborated, Theory}

/** An elaborated model with no structural problem. Only `Validate` makes one, so its takers need not check again. */
opaque type Valid = Elaborated

object Valid:
  private[analysis] def apply(e: Elaborated): Valid = e
  extension (v: Valid)
    def elaborated: Elaborated = v
    def theory: Theory = v.theory
