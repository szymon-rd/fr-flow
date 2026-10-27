package frflow.project.program

import frflow.*

/** The same knowledge base twice, its one claim's formula changed and its sentence not: what a decision binds must
  * move with the formula. And an example of it, written two ways.
  */
object Versions:
  object Before:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) >= 0))
    val kb = KnowledgeBase("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)

    class Shown extends FrFlowExamples(kb):
      example("one"):
        d(1) is 1

  object After:
    val d = Definition[BigInt => BigInt]("a number the service gives for another")
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) >= 1))
    val kb = KnowledgeBase("Steps")(nonNegative).implementTested(d)(_ => n => n.abs)

    class Shown extends FrFlowExamples(Before.kb):
      example("one"):
        d(2) is 2
