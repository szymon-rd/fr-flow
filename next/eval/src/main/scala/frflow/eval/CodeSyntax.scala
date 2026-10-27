package frflow.eval

import cats.effect.kernel.Async
import frflow.core.Elaborated
import frflow.core.code.Values
import frflow.core.example.Given
import frflow.dsl.example.Binding
import frflow.dsl.flow.{Flow, Terms}
import frflow.dsl.kb.KnowledgeBase
import frflow.dsl.vocab.Definition
import frflow.eval.run.Wiring

/** `knowledge.code(d)(grants := …)` and `knowledge.running[F](…)` in production: a Definition's code, built as its
  * tests build it (the values given, over the other Definitions' meanings: `run.Wiring`), and what a program runs
  * with. What `service` was, less the check: nothing checks a call in production.
  */
object CodeSyntax:
  extension (kb: KnowledgeBase)
    /** `d`'s meaning as plain code calls it (its plain Scala, its proven define run by the evaluator, its value), or
      * the value given it.
      */
    def code[F](d: Definition[F])(bindings: Binding*): F =
      CodeSyntax.values(kb, bindings).get(d.name).fold(throw IllegalArgumentException(
        s"FrFlow: ${d.name.value} has no meaning in ${kb.name.value} and is given none"))(v => Fn.as[F](ScalaValue(v)))

    /** What a program and its lifted adapters run with in production: `Running` over the values given. */
    def running[F[_]](bindings: Binding*)(using F: Async[F]): F[Flow[F] & Terms] =
      F.defer(F.widen(Running.make[F](CodeSyntax.values(kb, bindings))))

  /** Every Definition's meaning, and the values given, which win. */
  private def values(kb: KnowledgeBase, bindings: Seq[Binding]): Values =
    val e = elaborated(kb)
    val wiring = Wiring(Semantics(e), e.theory)
    wiring.values(wiring.supplied(bindings.toList.map(b => Given(b.of, b.value.fold(f =>
      throw IllegalArgumentException(s"FrFlow: the value given ${b.of.value} is not data: $f"), identity)))))

  private def elaborated(kb: KnowledgeBase): Elaborated = kb.elaborated.fold(errors =>
    throw IllegalArgumentException(s"FrFlow: ${kb.name.value} does not elaborate: ${errors.iterator.mkString("; ")}"),
    identity)
