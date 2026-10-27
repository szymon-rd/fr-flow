package frflow.eval

import cats.effect.kernel.Async
import frflow.dsl.flow.{Flow, Terms}
import frflow.dsl.kb.FrModel
import frflow.dsl.example.Binding
import frflow.dsl.vocab.Definition

/** `knowledge.code(d)(grants := …)` and `knowledge.running[F](…)` in production: a Definition's code, built as its
  * tests build it (the values given, over the other Definitions' meanings: `run.Wiring`), and what a program runs
  * with. What `service` was, less the check: nothing checks a call in production.
  */
object CodeSyntax:
  extension (kb: FrModel)
    def code[F](d: Definition[F])(bindings: Binding*): F = ???

    /** What a program and its lifted adapters run with in production: `Running` over the values given. */
    def running[F[_]: Async](bindings: Binding*): F[Flow[F] & Terms] = ???
