package frflow.cli

import frflow.*
import frflow.api.Shelf.{Before, d}

/** The API suites' shelf, changed as the CLI's suites need it. */
object Shelves:
  private val sameAboveSays = "Above zero, the service gives the number itself."

  /** The claim made stricter and its code unchanged: the code now fails it, at zero. */
  object Strict:
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) > 0))
    val sameAbove = Node.claim(sameAboveSays)(forall((n: Term[BigInt]) => (n > 0) implies (d(n) === n)))
      .refines(nonNegative)
    val kb = KnowledgeBase("Shelf")(nonNegative, sameAbove).implementTested(d)(_ => n => n.abs)

  /** The part taken out of the model. */
  object Fewer:
    val kb = KnowledgeBase("Shelf")(Before.nonNegative).implementTested(d)(_ => n => n.abs)

  /** Nothing yet. */
  object Empty:
    val kb = KnowledgeBase("Toy")()
