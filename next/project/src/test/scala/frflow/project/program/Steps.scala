package frflow.project.program

import frflow.*

/** Two small FrModels for the shell's suites: a step whose one part fixes the answer only above zero, so a
  * case below it refutes it (`nonNegative` from `sameAbove`); and code that throws, with an example of it.
  */
object Steps:
  val d = Definition[BigInt => BigInt]("a number the service gives for another")
  val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) >= 0))
  val sameAbove = Node.claim("Above zero, the service gives the number itself.")(
    forall((n: Term[BigInt]) => (n > 0) implies (d(n) === n))).refines(nonNegative)
  val steps = FrModel("Steps")(nonNegative, sameAbove).implementTested(d)(_ => n => n.abs)

  val boom = Definition[BigInt => BigInt]("a number the broken service gives")
  val nonZero = Node.claim("The broken service never gives zero.")(forall((n: Term[BigInt]) => boom(n) =!= 0))
  val broken = FrModel("Broken")(nonZero)
    .implementTested(boom)(_ => _ => throw IllegalStateException("the service is down"))

  class BrokenExamples extends FrFlowExamples(broken):
    example("one gives one"):
      boom(1) is 1
