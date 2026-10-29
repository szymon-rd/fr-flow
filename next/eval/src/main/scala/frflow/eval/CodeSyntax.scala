package frflow.eval

import cats.effect.kernel.Async
import frflow.core.Elaborated
import frflow.core.code.Values
import frflow.core.example.Given
import frflow.dsl.example.Binding
import frflow.dsl.flow.{Flow, Terms}
import frflow.dsl.kb.FrModel
import frflow.dsl.model.Implemented
import frflow.dsl.vocab.Definition
import frflow.eval.run.Wiring

/** `knowledge.code(d)(grants := …)` and `knowledge.running[F](…)` in production: a Definition's code, built as its
  * tests build it (the values given, over the other Definitions' meanings: `run.Wiring`), and what a program runs
  * with. What `service` was, less the check: nothing checks a call in production.
  */
object CodeSyntax:
  extension (kb: FrModel)
    /** `d`'s meaning as plain code calls it (its plain Scala, its proven define run by the evaluator, its value), or
      * the value given it.
      */
    def code[F](d: Definition[F])(bindings: Binding*): F =
      CodeSyntax.values(kb, bindings).get(d.name).fold(throw IllegalArgumentException(
        s"FrFlow: ${d.name.value} has no meaning in ${kb.name.value} and is given none"))(v => Fn.as[F](ScalaValue(v)))

    /** What a program runs with in production: `Running` over the values given, each model's operations their Scala
      * of the value given (`storedBookings := table`).
      */
    def running[F[_]](bindings: (Binding | Implemented)*)(using F: Async[F]): F[Flow[F] & Terms] =
      F.defer {
        val e = elaborated(kb)
        val values = CodeSyntax.values(kb, bindings.collect { case b: Binding => b })
        F.widen(Running.make[F](values, Literals(e), Bound.of[F](e.theory, bindings.toList.collect {
          case i: Implemented => i })))
      }

  /** Every Definition's meaning, and the values given, which win. */
  private def values(kb: FrModel, bindings: Seq[Binding]): Values =
    val e = elaborated(kb)
    val wiring = Wiring(Semantics(e), e.theory)
    wiring.values(wiring.supplied(bindings.toList.map(b => Given(b.of, b.value.fold(f =>
      throw IllegalArgumentException(s"FrFlow: the value given ${b.of.value} is not data: $f"), identity)))))

  private def elaborated(kb: FrModel): Elaborated = kb.elaborated.fold(errors =>
    throw IllegalArgumentException(s"FrFlow: ${kb.name.value} does not elaborate: ${errors.iterator.mkString("; ")}"),
    identity)
