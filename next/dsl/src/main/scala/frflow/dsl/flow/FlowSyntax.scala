package frflow.dsl.flow

import frflow.core.term.World
import frflow.dsl.term.{LeanType, Term}

/** The combinators as programs write them on a pair: `(a, b).parTupled`; and, in a flow claim, a run from a world
  * (`runExpiry(now).from(before) { … }`).
  */
object FlowSyntax:
  extension [R: LeanType](run: Term[Flow[R]])
    def from(before: Term[World]): RunFrom[R] = RunFrom(run, before)

  extension [A: LeanType, B: LeanType](p: (Flow[A], Flow[B]))
    def parTupled: Flow[(A, B)] = Flow.parTupled(p._1, p._2)
