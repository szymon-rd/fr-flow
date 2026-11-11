package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The processor: it handles one payment from the log. It has the limits service decide it, has the accounts
  * service post it if it is approved, and only then commits the position past it. Each step can be repeated, so a
  * payment delivered again, to this instance after a crash or to another after a rebalance, is applied once.
  */
final class Processor(limits: Limits^, accounts: Accounts^, checkpoint: Checkpoint^):
  def handle(p: Payment): Boolean =
    val approved = limits.authorise(p)
    if approved then accounts.post(p)
    checkpoint.commit(p.offset)
    approved

object Processor:
  /** The state the processor works on: its three services' stores'. */
  type State = Pipeline

  /** What other calls may do between two steps of handling a payment: leave it undisturbed. */
  val others = lifted { (p: Payment, before: Pipeline, after: Pipeline) => undisturbed(p.id, before, after) }

  /** Handling a payment alone, as the statements speak of it: from the pipeline, whether it is approved, with
    * the pipeline after.
    */
  val handle = Definition[(Pipeline, Payment) -> (Boolean, Pipeline)]("handling a payment, alone: whether it " +
    "is approved, and the pipeline after")

  /** Handling a payment among other calls: from the pipeline and what the others leave before each step
    * (`between`, by the step's number), the answer with every step taken: the pipeline the step started from and
    * the one it left. A crash is the call stopping after any of its steps.
    */
  val handleAmongOthers =
    Definition[(Pipeline, Map[BigInt, Pipeline], Payment) -> (Boolean, List[(Pipeline, Pipeline)])](
      "handling a payment among other calls: its answer, and each of its steps")

  val handleCode = updating { (processor: Processor^, p: Payment) => processor.handle(p) }
  val handleAmongOthersCode = interleaving { (processor: Processor^, p: Payment) => processor.handle(p) }(others)

  // Alone, from any pipeline: one a crash left half-way among them.

  val handledIsApplied = Node.claim("A payment handled is applied: decided, and posted if approved.")(
    forall((pipeline: Term[Pipeline], p: Term[Payment]) => Pipeline.applied(handle(pipeline, p)._2, p.id)))

  val positionMovesPastTheHandled = Node.claim("Handling the payment the position is at moves the position " +
      "one past it.")(
    forall((pipeline: Term[Pipeline], p: Term[Payment]) =>
      (pipeline.committed === p.offset) implies (handle(pipeline, p)._2.committed === p.offset + 1)))

  val redeliveryChangesNothing = Node.claim("A payment handled again gets the answer it got and changes " +
      "nothing.")(
    forall((pipeline: Term[Pipeline], p: Term[Payment]) =>
      handle(handle(pipeline, p)._2, p) === handle(pipeline, p)))

  val fittingIsApproved = Node.claim("A payment not yet decided that fits its card's limit of the day is " +
      "approved.")(
    forall((pipeline: Term[Pipeline], p: Term[Payment]) =>
      (!Spending.decided(pipeline.spending, p.id) &&
        Spending.spent(pipeline.spending.decisions, p.card, p.day) + p.amount <= pipeline.spending.limit) implies
        handle(pipeline, p)._1))

  // Among other calls: each holds of every step, whatever the others do between steps.

  val neverOverTheLimit = Node.claim("Handling a payment leaves no card over its limit at any step, whatever " +
      "other calls do between them.")(
    forall((pipeline: Term[Pipeline], between: Term[Map[BigInt, Pipeline]], p: Term[Payment]) =>
      Spending.withinLimits(pipeline.spending) implies
        handleAmongOthers(pipeline, between, p)._2.forall(step => Spending.withinLimits(step._2.spending))))

  val moneyIsConserved = Node.claim("No step of handling a payment makes money or destroys it.")(
    forall((pipeline: Term[Pipeline], between: Term[Map[BigInt, Pipeline]], p: Term[Payment]) =>
      handleAmongOthers(pipeline, between, p)._2.forall(step =>
        Books.total(step._2.books.postings) === Books.total(step._1.books.postings))))

  val postedOnce = Node.claim("No step of handling a payment adds to the postings of a payment that has some, " +
      "whatever other calls do between its steps.")(
    forall((pipeline: Term[Pipeline], between: Term[Map[BigInt, Pipeline]], id: Term[String], p: Term[Payment]) =>
      Books.orderly(pipeline.books) implies handleAmongOthers(pipeline, between, p)._2.forall(step =>
        Books.made(step._1.books.postings, id).isEmpty ||
          Books.made(step._2.books.postings, id) === Books.made(step._1.books.postings, id))))

  val neverCommitsAhead = Node.claim("No step moves the position but the last, from the payment's offset to " +
      "one past it, and by then the payment is applied: a crash after any step loses no payment.")(
    forall((pipeline: Term[Pipeline], between: Term[Map[BigInt, Pipeline]], p: Term[Payment]) =>
      handleAmongOthers(pipeline, between, p)._2.forall(step =>
        step._2.committed === step._1.committed ||
          (step._1.committed === p.offset && step._2.committed === p.offset + 1 &&
            Pipeline.applied(step._2, p.id)))))

  // What handling a payment grants other calls: what it relies on of them (`others`), each of its steps keeps.

  val leavesOthersUndisturbed = Node.claim("Each step of handling a payment leaves every payment undisturbed: " +
      "no card over its limit, the books orderly, what was decided decided as it was, what was posted posted.")(
    forall((pipeline: Term[Pipeline], between: Term[Map[BigInt, Pipeline]], other: Term[String],
        p: Term[Payment]) =>
      (Spending.withinLimits(pipeline.spending) && Books.orderly(pipeline.books)) implies
        handleAmongOthers(pipeline, between, p)._2.forall(step => undisturbed(other, step._1, step._2))))
