package frflow.eval.run

import frflow.core.code.Values
import frflow.core.Elaborated
import frflow.core.example.Given
import frflow.dsl.example.Binding
import frflow.dsl.kb.FrModel
import frflow.dsl.vocab.Declaration
import frflow.eval.{Fn, ScalaValue}
import frflow.eval.run.Wiring
import frflow.eval.term.Semantics

/** `knowledge.code(d)(grants := …)` in production: a Definition's code, built as its tests build it (the values
  * given, over the other Definitions' meanings: `run.Wiring`). Nothing checks a call in production.
  */
object CodeSyntax:
  extension (kb: FrModel)
    /** `d`'s meaning as plain code calls it (its plain Scala, its proven define run by the evaluator, its value), or
      * the value given it.
      */
    def code[F](d: Declaration[F])(bindings: Binding*): F =
      CodeSyntax.values(kb, bindings).get(d.name).fold(throw IllegalArgumentException(
        s"FrFlow: ${d.name.value} has no meaning in ${kb.name.value} and is given none"))(v => Fn.as[F](ScalaValue(v)))

  /** Every Definition's meaning, and the values given, which win. */
  private def values(kb: FrModel, bindings: Seq[Binding]): Values =
    val e = elaborated(kb)
    val wiring = Wiring(Semantics(e), e.theory)
    wiring.values(wiring.supplied(bindings.toList.map(b => Given(b.of, b.value.fold(f =>
      throw IllegalArgumentException(s"FrFlow: the value given ${b.of.value} is not data: $f"), identity)))))

  private def elaborated(kb: FrModel): Elaborated = kb.elaborated.fold(errors =>
    throw IllegalArgumentException(s"FrFlow: ${kb.name.value} does not elaborate: ${errors.iterator.mkString("; ")}"),
    identity)
