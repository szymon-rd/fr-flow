# Payments: a stream handler proven through redelivery, a crash and a second instance

A consumer reads card payments from a log and, for each, checks the card's daily limit, posts the money, and
commits its offset. Every team that has written one knows the ways it goes wrong:

- **A crash loses a payment.** The offset was committed before the payment was posted.
- **A redelivery charges twice.** The log delivers at least once, and the posting was not guarded.
- **Two instances take a card over its limit.** After a rebalance both run; each checks the limit, each approves.

None of them shows in a test that runs one call to its end. This example writes the consumer as ordinary Scala
and has Rocq prove what must hold of it. The log itself is not implemented: that it delivers at least once, in
order, is a decision the model names.

## The code

Four interfaces, each with the members such a service has, and nothing added for the proofs:

```scala
trait PaymentHandler extends Mutable:
  /** Handles one payment: has it authorised, posts it if it is approved, and commits its offset. */
  update def handle(payment: Payment): Boolean

trait CardLimits extends Mutable:        // authorise, decided, approved, spent, dailyLimit
trait Ledger extends Mutable:            // post, posted, postingsOf, total
trait ConsumerOffsets extends Mutable:   // commit, committed

final class StreamPaymentHandler(limits: CardLimits^, ledger: Ledger^, offsets: ConsumerOffsets^)
    extends PaymentHandler:
  update def handle(payment: Payment): Boolean =
    val approved = limits.authorise(payment)
    if approved then ledger.post(payment)
    offsets.commit(payment.offset)
    approved
```

The traits extend Scala's `caps.Mutable` and mark what changes them `update`. That is Scala's own: it lets the
compiler check, under capture and separation checking, that a service is not aliased where it is held
(`Ledger^`), so FrFlow may read a method that changes it as a function from its state to its state. Ids are
opaque types (`PaymentId`, `CardId`, `MerchantId`), so one is never given where another is meant.

## The claims

Each trait is declared as a word of the model (`Declaration[Ledger]("…")`: a structure, a value with members),
and a claim is an ordinary `Node.claim` written through the members:

```scala
object Ledger:
  val ledger = Declaration[Ledger]("the ledger: each payment posted to the books once")

  val postIsRepeatable = Node.claim("Posting a payment again changes nothing.")(
    forall((p: Term[Payment]) => ledger.post(p).in(ledger.post(p).after).after === ledger.post(p).after))
```

A member that changes the structure (`update`) has a `result` and the structure `after` it; any member can be
asked `in` a given state; called plainly it is asked of the structure as it stands. A claim holds in every state.

What matters about `handle` is what it does to the ledger, the limits and the offsets. So the claims on the
handler are said through *their* interfaces, asked as the handler has them:

```scala
val moneyIsConserved = Node.claim("Handling a payment makes no money and destroys none.")(
  forall((p: Term[Payment]) => ledger.total.in(handler.handle(p).after) === ledger.total))
```

`ledger.total.in(handler.handle(p).after)` is the total of the ledger the handler holds, after the call; the
plain `ledger.total` beside it is that same ledger as it stands. What a claim needs more than once is a
definition in the model, not a member of a trait: "a payment is applied" is `PaymentHandler.applied`, decided and
posted if approved.

## The model

```scala
val payments: FrModel = FrModel("Payments")(…,
  limits.define(lifted[RecordedLimits]),
  ledger.define(lifted[PostingLedger]),
  offsets.define(lifted[CommittedOffset]),
  handler.define(lifted[StreamPaymentHandler](limits, ledger, offsets)))
```

The model lists each word's Definition beside its nodes: the class, named by its type. A class that holds
structures is given the word of each, in the order its constructor takes them; that is also what says which
ledger a claim on the handler speaks of. In Rocq the handler's code is a function of *any* `authorise`, `post`
and `commit`, and its claims are proven from the claims on `limits`, `ledger` and `offsets`, not from the classes'
bodies. Another class given for `ledger` (one over a database) is held to the same claims; the handler's proofs
do not change.

| File | What it holds |
| --- | --- |
| `Ids.scala` | `PaymentId`, `CardId`, `MerchantId`: opaque types over a string |
| `Domain.scala` | `Payment` (contract: the amount is positive), `Decision`, `Account`, `Posting` |
| `CardLimits.scala`, `Ledger.scala`, `ConsumerOffsets.scala` | Each: the trait, its word and claims in the companion, a class |
| `PaymentHandler.scala` | The handler: the trait, its word, the claims on it, the class |
| `EagerHandler.scala`, `HastyHandler.scala` | Two first versions of the handler, each with one of the bugs |
| `Payments.scala` | The model: which claim rests on which, each word's Definition, what is trusted |

## Every step of a call: a crash, a second instance

`handle` makes three calls of what it holds. Each is a step: a crash may stop the call after any of them, and
after a rebalance another instance may run its own steps in between. A call in a claim has its steps:

```scala
val noStepMakesMoney = Node.claim("No step of handling a payment makes money or destroys it.")(
  forall((p: Term[Payment]) =>
    handler.handle(p).amongOthers(run => run.steps.forall(step =>
      ledger.total.in(step._2) === ledger.total.in(step._1)))))
```

- `call.steps` is each step that changes the structure: the structure as the step found it, and as it left it. A
  class that holds no structure makes its change in one step; a class made of structures takes one for each call
  it makes of them.
- `call.amongOthers(run => …)` says what holds of the call whatever other calls do between its steps: before each
  step but the first they may have left the structure in any state at all. `run.others` is what they did, so a claim
  can say what it takes of them (`neverCommitsAhead`: they leave a payment decided as it was, and posted if it
  was). `call.among(between)` is the same under one schedule.
- What a call takes of the others, each of its own steps grants (`everyStepLeavesOthersUndisturbed`): so it holds
  among calls of the same structure.

Redelivery is the member called again (`redeliveryChangesNothing`); recovery after a crash is redelivery from the
state the crash left, and `handledIsApplied` holds from any state.

## What is proven

| Claim | Says | Proof |
| --- | --- | --- |
| `PaymentHandler.handledIsApplied` | A payment handled is decided, and posted if approved, from any state | automatic |
| `PaymentHandler.appliedStaysApplied` | Handling a payment leaves every payment applied before applied | automatic |
| `PaymentHandler.offsetMovesPastTheHandled` | Handling the payment at the committed offset moves it one past | automatic |
| `PaymentHandler.redeliveryChangesNothing` | Handled again, a payment gets the answer it got and changes nothing | by hand |
| `PaymentHandler.fittingIsApproved` | A new payment that fits the limit is approved | automatic |
| `PaymentHandler.handlingKeepsWithinLimit` | A card within its limit of a day stays within it | automatic |
| `PaymentHandler.moneyIsConserved` | Handling a payment makes no money and destroys none | automatic |
| `PaymentHandler.handlingKeepsMarks`, `postedOnce` | A payment with postings stays marked, and gets no more | automatic |
| `PaymentHandler.everyStepKeepsWithinLimit` | No step takes a card over its limit, whatever other calls do between | automatic |
| `PaymentHandler.noStepMakesMoney` | No step makes money or destroys it | automatic |
| `PaymentHandler.noStepPostsTwice` | No step adds to the postings of a payment that has some | automatic |
| `PaymentHandler.everyStepLeavesOthersUndisturbed` | Each step leaves what was decided decided, what was posted posted | automatic |
| `PaymentHandler.neverCommitsAhead` | No step moves the committed offset but one that leaves the payment applied: a crash after any step loses no payment | by hand |
| `CardLimits.authorisedIsRecorded`, `authoriseIsRepeatable` | The answer is what is recorded; a second call changes nothing | automatic |
| `CardLimits` (3 more), `Ledger` (6), `ConsumerOffsets` (2) | What each call does and keeps | automatic |
| `EagerHandler.eagerAppliesThePayment`, `HastyHandler.hastyPostsWhatItApproves` | What each first version does right | automatic |

29 claims: 27 by FrFlow's own tactic, 2 by hand (`redeliveryChangesNothing`, `neverCommitsAhead`). The hand
proofs are under `rocq/Proofs/Payments/`. Rocq checks both kinds; no proof is given up (`Admitted`) or rests on
anything but classical logic and extensionality (`docs/ROCQ.md`). Of the 22 conditions the claims are stated
under, 16 are shown possible; the six over the handler's steps among other calls are not yet.

One statement is trusted and marked as a design decision in the model, for the developer to accept or reject:
`deliveryIsAtLeastOnce`, that the log delivers every payment, in order from the committed position, and again
after a restart.

## The two first versions

Each is the handler with its lines in another order, defines a word of its own, does one thing
provably right, and passes any test of one call run to its end. An example shows what it gets wrong.

| Version | The difference | Proven of it | What an example shows |
| --- | --- | --- | --- |
| `CommitFirstHandler` | Commits first | Run to its end it leaves the payment applied | Stopped after its first step, the committed offset is past a payment never applied |
| `CheckThenActHandler` | Reads what the card spent and the limit, decides itself, then has the payment recorded | A payment it approves is posted | Another payment approved between its check and its record: it approves and posts a payment the card limits declined |

There is no version that charges twice on redelivery: the handler cannot. Posting once is the ledger's
(`postIsRepeatable`), and a class given for `ledger` that did not keep it would fail that proof.

The examples are in `PaymentsExamples`. A state is given as an object of the class that implements the trait:

```scala
private val start = handler.holding(
  StreamPaymentHandler(RecordedLimits(BigInt(100), Nil), PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))

example("a payment within the limit: approved, posted, its offset committed"):
  val done = handler.handle(coffee).in(start)
  done.result && (ledger.postingsOf(p1).in(done.after) is charged) &&
    (offsets.committed.in(done.after) is BigInt(1))
```

The Scala evaluator computes each of the eight on the code read from the classes. Proving each from the
definitions printed from them is not done in Rocq yet: `check` reports each as holding on the code and not decided
by the claims.

## Running it

```bash
sbt "testing/testOnly frflow.eval.PaymentsSuite"
```

```bash
sbt "project/Rocq/testOnly frflow.project.services.PaymentsRocqSuite"
```

```bash
bin/frflow payments check
```

The first checks the model is valid, that the examples hold of the code, and that the classes run as the Scala
they are. The second and third run Rocq: every claim proven, every example held on the code. The nodes are proposed, not
accepted: deciding them is the developer's, with their signing key.

## What this does not cover

- **State invariants as such.** A claim is said of the structure in every state, so "no card is over its limit" is
  stated as what each call, and each step, keeps, not as a fact of every state.
- **The whole log as one theorem.** What is proven is the step: each call leaves its payment applied and moves the
  committed offset only past it. "Every payment below the committed offset is applied" follows by induction over
  the log, which rests on `deliveryIsAtLeastOnce` and is not carried out in Rocq.
- **A step is a call of a held structure.** That each such call is one transaction is the held structure's to keep:
  a class over a database does it with a transaction, and the model does not check that it does.
- **One class for a trait.** A model gives one class for each structure's trait, so a second implementation of
  `Ledger` cannot stand beside the first in this model; that is why the two first versions have traits of their
  own (`EagerHandler`, `HastyHandler`) where plain Scala would have them implement `PaymentHandler`.
- **Amounts, days and offsets are plain numbers.** Only ids have types of their own; the reader does not yet read
  arithmetic on an opaque type.
- **A class FrFlow cannot read.** `defineTested` for a structure, a class tested against the claims, is not
  built; nor is the classes' Scala tested against the terms read from them on generated cases.
- **A member no claim mentions** has its code, and nothing is proven of it.
- **The breaking schedules are written by hand.** Rocq proves or does not; nothing searches for the schedule.
- **One kind of event, one payment per call, a daily limit.** No refunds, no batches (the reader has no loops), no
  sliding window.
- **Liveness.** Nothing says a call finishes.
- **`IO`-style code.** The reader takes direct style; cats-effect values are invisible to the separation checker
  ([docs/SEPARATION-SPIKE.md](../../docs/SEPARATION-SPIKE.md)).
