# Payments: a stream processor whose services are Definitions

A consumer reads card payments from a log and, for each, checks the card's daily limit, posts the money, and
commits its position. The log delivers at least once, so a payment may be handled twice; and what goes wrong in
such a consumer is known: a redelivery charges twice, a card goes over its limit, money is made or lost.

This example writes the consumer as ordinary Scala services and has Lean prove what must hold of them. It is the
example of the service shape:

- **A trait** says what members a service has. It extends nothing of FrFlow's.
- **A `Definition` of the trait's type** is the service in the model.
- **The claims** are ordinary `Node.claim`s on that Definition, written through its members.
- **A class that implements the trait** is the value given for the Definition (`implementProven`). FrFlow reads the
  class into Lean, and Lean proves it meets every claim on the Definition.

## A service

```scala
trait Limits extends Mutable:
  update def authorise(p: Payment): Boolean
  def decided(id: String): Boolean
  def approved(id: String): Boolean
  def spent(card: String, day: BigInt): BigInt
  def limit: BigInt

object Limits:
  val limits = Definition[Limits]("the limits service: it decides each payment against its card's limit of the day")

  val authorisedIsRecorded = Node.claim("A payment authorised is decided, and the answer is the decision recorded.")(
    forall((p: Term[Payment]) =>
      limits.decided(p.id).in(limits.authorise(p).after) &&
        (limits.authorise(p).result === limits.approved(p.id).in(limits.authorise(p).after))))

final class SpendLimits(val limit: BigInt, var decisions: List[Decision]) extends Limits:
  update def authorise(p: Payment): Boolean =
    val fits = spent(p.card, p.day) + p.amount <= limit
    if !decided(p.id) then decisions = decisions :+ Decision(p.id, p.card, p.day, p.amount, fits)
    approved(p.id)
  …
```

In a claim, a member is called as the trait declares it. A member that changes the service (`update`) has a
`result` and the service `after` it; any member can be asked `in` a given state of the service
(`limits.decided(id).in(limits.authorise(p).after)`); called plainly it is asked of the service as it stands. A
claim holds of the service in every state: FrFlow binds "the service as it stands" under a `forall`.

The trait extends Scala's `caps.Mutable` and marks what changes it `update`. That is Scala's own, and it is what
lets the compiler check, under capture and separation checking, that a service is not aliased where it is held
(`Limits^`), so that FrFlow may read a method that changes it as a function from the service to the service.

## A service made of services

```scala
final class StreamProcessor(limits: Limits^, accounts: Accounts^, checkpoint: Checkpoint^) extends Processor:
  update def handle(p: Payment): Boolean =
    val approved = limits.authorise(p)
    if approved then accounts.post(p)
    checkpoint.commit(p.offset)
    approved
```

The model gives each Definition its class. The processor is made with the other services' Definitions:

```scala
val payments: FrModel = FrModel("Payments")(…)
  .implementProven(limits)(lifted(SpendLimits(BigInt(100), Nil)))
  .implementProven(accounts)(lifted(LedgerAccounts(Nil, Nil)))
  .implementProven(checkpoint)(lifted(OffsetCheckpoint(BigInt(0))))
  .implementProven(processor)(lifted(StreamProcessor(limits, accounts, checkpoint)))
```

So in Lean the processor's code is a function of *any* `authorise`, `post` and `commit`, and its claims are proven
from the claims on `limits`, `accounts` and `checkpoint`, not from `SpendLimits`' body. Another class given for
`limits` (one over a database) is held to the same claims; the processor's proofs do not change.

| File | What it holds |
| --- | --- |
| `Domain.scala` | `Payment` (contract: the amount is positive), `Decision`, `Posting` |
| `Limits.scala`, `Accounts.scala`, `Checkpoint.scala` | A service each: the trait, its Definition and claims in the companion, the class |
| `Processor.scala` | The processor: the same, over the three services |
| `Payments.scala` | The model: which claim rests on which, the class given for each Definition, what is trusted |

## Every step of a call: a crash, a second instance

`handle` makes three calls of other services. Each is a step: a crash may stop the call after any of them, and
after a rebalance another instance may run its own steps in between. A call in a claim has its steps:

```scala
val noStepMakesMoney = Node.claim("No step of handling a payment makes money or destroys it.")(
  forall((p: Term[Payment]) =>
    processor.handle(p).amongOthers(run => run.steps.forall(step =>
      processor.total.in(step._2) === processor.total.in(step._1)))))
```

- `call.steps` is each step the call takes: the service as the step found it, and as it left it. A class that
  holds no service makes its change in one step; a class made of services takes one for each call it makes of them.
- `call.amongOthers(run => …)` says what holds of the call whatever other calls do between its steps: before each
  step but the first they may have left the service in any state at all. `run.others` is what they did, so a claim
  can say what it takes of them (`neverCommitsAhead`: they leave a payment decided as it was, and posted if it
  was). `call.among(between)` is the same under one schedule.
- What a call takes of the others, each of its own steps grants (`everyStepLeavesOthersUndisturbed`): so it holds
  among calls of the same service.

## What is proven

| Claim | Says | Proof |
| --- | --- | --- |
| `Processor.handledIsApplied` | A payment handled is decided, and posted if approved, from any state | automatic |
| `Processor.appliedStaysApplied` | Handling a payment leaves every payment applied before applied | automatic |
| `Processor.positionMovesPastTheHandled` | Handling the payment the position is at moves it one past | automatic |
| `Processor.redeliveryChangesNothing` | Handled again, a payment gets the answer it got and changes nothing | automatic |
| `Processor.fittingIsApproved` | A new payment that fits the limit is approved | automatic |
| `Processor.handlingKeepsWithinLimit` | A card within its limit of a day stays within it | automatic |
| `Processor.moneyIsConserved` | Handling a payment makes no money and destroys none | automatic |
| `Processor.handlingKeepsMarks`, `postedOnce` | A payment with postings stays marked, and gets no more | automatic |
| `Processor.everyStepKeepsWithinLimit` | No step takes a card over its limit, whatever other calls do between | automatic |
| `Processor.noStepMakesMoney` | No step makes money or destroys it | automatic |
| `Processor.noStepPostsTwice` | No step adds to the postings of a payment that has some | automatic |
| `Processor.everyStepLeavesOthersUndisturbed` | Each step leaves what was decided decided, what was posted posted | automatic |
| `Processor.neverCommitsAhead` | No step moves the position but one that leaves the payment applied: a crash after any step loses no payment | by hand |
| `Limits.authorisedIsRecorded`, `authoriseIsRepeatable` | The answer is what is recorded; a second call changes nothing | by hand |
| `Limits` (3 more), `Accounts` (6), `Checkpoint` (2) | What each call does and keeps | automatic |

27 claims: 24 by FrFlow's own tactic, 3 by hand (`lean/Proofs/Payments/`: three proofs over two lemmas, and the
witnesses in `Whole.lean`, about 170 lines of Lean). Lean checks both kinds; no proof uses `sorry` or an axiom
beyond Lean's standard three.

One statement is trusted and marked as a design decision in the model, for the developer to accept or reject:
`deliveryIsAtLeastOnce`, that the log delivers every payment, in order from the committed position, and again
after a restart.

## Running it

```bash
sbt "testing/testOnly frflow.eval.PaymentsSuite"
```

```bash
sbt "project/Lean/testOnly frflow.project.services.PaymentsLeanSuite"
```

```bash
bin/frflow payments check
```

The first checks the model is valid. The second and third run Lean: every claim proven. The nodes are proposed,
not accepted: deciding them is the developer's, with their signing key.

## What this does not cover

- **State invariants as such.** A claim is said of the service in every state, so "no card is over its limit" is
  stated as what each call keeps (`handlingKeepsWithinLimit`), not as a fact of every state.
- **The whole log as one theorem.** What is proven is the step: each call leaves its payment applied and moves the
  position only past it. "Every payment below the position is applied" follows by induction over the log, which
  rests on `deliveryIsAtLeastOnce` and is not carried out in Lean.
- **A member no claim mentions** is given no code to check: nothing is proven of it.
- **A step is a call of a held service.** That each such call is one transaction is the held service's to keep:
  a class over a database does it with a transaction, and the model does not check that it does.
- **One kind of event, one payment per call, a daily limit.** No refunds, no batches (the reader has no loops), no
  sliding window.
- **Liveness.** Nothing says a call finishes.
- **`IO`-style code.** The reader takes direct style; cats-effect values are invisible to the separation checker
  ([docs/SEPARATION-SPIKE.md](../../docs/SEPARATION-SPIKE.md)).
