package frflow.dsl.example

import frflow.dsl.term.{Lift, Reify, Term}
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.vocab.Definition

/** What an example's fact is written with (`FrFlowExamples`): `granted(…) is true`, `t is value`, and a value given
  * to a provided Definition, `example("Alice gets in", grants := List(Grant(alice, a)))(…)`.
  */
object ExampleSyntax:
  extension [A](d: Definition[A])
    /** The value an example gives `d`. */
    def :=(value: A): Binding = Binding(d.name, Reify(d.leanType, value))

  extension (t: Term[Boolean])
    /** That the term holds (`is true`) or does not (`is false`). */
    infix def is(holds: Boolean): Term[Boolean] = if holds then t else !t

  extension [A](t: Term[A])
    /** That the term's value is `value`. */
    infix def is(value: A): Term[Boolean] = t === Lift.constant(value)(using t.leanType)
