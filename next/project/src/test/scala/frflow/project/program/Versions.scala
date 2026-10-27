package frflow.project.program

import frflow.*
import frflow.dsl.vocab.Stating

/** The same FrModel twice, its one claim's formula changed and its sentence not: what a decision binds must
  * move with the formula. And an example of it, written two ways.
  */
object Versions:
  object Before:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) >= 0))
    val kb = FrModel("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)

    class Shown extends FrFlowExamples(kb):
      example("one"):
        d(1) is 1

  object After:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) >= 1))
    val kb = FrModel("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)

    class Shown extends FrFlowExamples(Before.kb):
      example("one"):
        d(2) is 2

  /** `Before`'s formula with its Scala spaced out, and with its variable renamed: what it means is the same. */
  object Spaced:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) =>
      d(n)   >=   0))
    val kb = FrModel("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)

  object Renamed:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((m: Term[BigInt]) => d(m) >= 0))
    val kb = FrModel("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)

  /** A formula written through a helper of the developer's (`rule`), the same call each time, its body changed. */
  object Helped:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    private def rule(using Stating): Term[Boolean] = forall((n: Term[BigInt]) => d(n) >= 0)
    val nonNegative = Node.claim("The service never gives a negative number.")(rule)
    val kb = FrModel("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)

  object HelpedAgain:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    private def rule(using Stating): Term[Boolean] = forall((n: Term[BigInt]) => d(n) >= 1)
    val nonNegative = Node.claim("The service never gives a negative number.")(rule)
    val kb = FrModel("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)
