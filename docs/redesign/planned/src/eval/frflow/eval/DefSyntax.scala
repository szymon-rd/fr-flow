package frflow.eval

import frflow.dsl.term.Def

/** `d.fn` in plain code: the define as a Scala function, elaborated and compiled on first use (`Def.compiled`). */
object DefSyntax:
  extension [A, R](d: Def[A => R]) def fn: A => R = ???
  // … for 0 to 6 inputs.
