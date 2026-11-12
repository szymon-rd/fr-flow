# Payments: a stream processor whose services are declared, then defined

A consumer reads card payments from a log and, for each, checks the card's daily limit, posts the money, and
commits its position. Every team that has written one knows the ways it goes wrong:

- **A crash loses a payment.** The position was committed before the payment was posted.
- **A redelivery charges twice.** The log delivers at least once, and the posting was not guarded.
- **Two instances take a card over its limit.** After a rebalance both run; each checks the limit, each approves.

None of them shows in a test that runs one call to its end. This example writes the consumer as ordinary Scala
services and has Lean prove what must hold of them. The log itself is not implemented: that it delivers at least
once, in order, is a decision the model names.

It is the example of the service shape:

- **A trait** says what members a service has. It extends nothing of FrFlow's.
- **A `Declaration` of the trait's type** is the service in the model.
- **The claims** are ordinary `Node.claim`s on that word, written through its members.
- **A class that implements the trait** is its Definition (`limits.define(lifted[SpendLimits])`), listed in the
  model beside the nodes. FrFlow reads the class into Lean, and Lean proves it meets every claim on the word.

## A service

```scala
trait Limits extends Mutable:
  update def authorise(p: Payment): Boolean
  def decided(id: String): Boolean
  def approved(id: String): Boolean
  def spent(card: String, day: BigInt): BigInt
  def limit: BigInt

object Limits:
  val limits = Declaration[Limits]("the limits service: it decides each payment against its card's limit of the day")

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

The model lists each service's Definition beside its nodes: the class, named by its type. A class that holds
services is given the word of each, in the order its constructor takes them:

```scala
val payments: FrModel = FrModel("Payments")(…,
  limits.define(lifted[SpendLimits]),
  accounts.define(lifted[LedgerAccounts]),
  checkpoint.define(lifted[OffsetCheckpoint]),
  processor.define(lifted[StreamProcessor](limits, accounts, checkpoint)))
```

So in Lean the processor's code is a function of *any* `authorise`, `post` and `commit`, and its claims are proven
from the claims on `limits`, `accounts` and `checkpoint`, not from `SpendLimits`' body. Another class given for
`limits` (one over a database) is held to the same claims; the processor's proofs do not change.

| File | What it holds |
| --- | --- |
| `Domain.scala` | `Payment` (contract: the amount is positive), `Decision`, `Posting` |
| `Limits.scala`, `Accounts.scala`, `Checkpoint.scala` | A service each: the trait, its Declaration and claims in the companion, the class |
| `Processor.scala` | The processor: the same, over the three services |
| `Eager.scala`, `Hasty.scala` | Two first versions of the processor, each with one of the bugs |
| `Payments.scala` | The model: which claim rests on which, each service's Definition, what is trusted |

## Every step of a call: a crash, a second instance

`handle` makes three calls of other services. Each is a step: a crash may stop the call after any of them, and
after a rebalance another instance may run its own steps in between. A call in a claim has its steps:

```scala
val noStepMakesMoney = Node.claim("No step of handling a payment makes money or destroys it.")(
  forall((p: Term[Payment]) =>
    processor.handle(p).amongOthers(run => run.steps.forall(step =>
      processor.total.in(step._2) === processor.total.in(step._1)))))
```

- `call.steps` is each step that changes the service: the service as the step found it, and as it left it. A class
  that holds no service makes its change in one step; a class made of services takes one for each call it makes
  of them.
- `call.amongOthers(run => …)` says what holds of the call whatever other calls do between its steps: before each
  step but the first they may have left the service in any state at all. `run.others` is what they did, so a claim
  can say what it takes of them (`neverCommitsAhead`: they leave a payment decided as it was, and posted if it
  was). `call.among(between)` is the same under one schedule.
- What a call takes of the others, each of its own steps grants (`everyStepLeavesOthersUndisturbed`): so it holds
  among calls of the same service.

Redelivery is the member called again (`redeliveryChangesNothing`); recovery after a crash is redelivery from the
state the crash left, and `handledIsApplied` holds from any state.

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
| `Eager.eagerAppliesThePayment`, `Hasty.hastyPostsWhatItApproves` | What each first version does right | automatic |

29 claims: 26 by FrFlow's own tactic, 3 by hand. The hand proofs, two lemmas, the witnesses and the examples'
proofs are about 260 lines of Lean under `lean/Proofs/Payments/`. Lean checks both kinds; no proof uses `sorry` or
an axiom beyond Lean's standard three.

One statement is trusted and marked as a design decision in the model, for the developer to accept or reject:
`deliveryIsAtLeastOnce`, that the log delivers every payment, in order from the committed position, and again
after a restart.

## The two first versions

Each is the processor with its lines in another order, defines a word of its own, does one thing
provably right, and passes any test of one call run to its end. An example shows what it gets wrong.

| Version | The difference | Proven of it | What an example shows |
| --- | --- | --- | --- |
| `EagerProcessor` | Commits first | Run to its end it leaves the payment applied | Stopped after its first step, the position is past a payment never applied |
| `HastyProcessor` | Reads what the card spent and the limit, decides itself, then has the payment recorded | A payment it approves is posted | Another payment approved between its check and its record: it approves and posts a payment the limits service declined |

There is no version that charges twice on redelivery: the processor cannot. Posting once is the accounts
service's (`postIsRepeatable`), and a class given for `accounts` that did not keep it would fail that proof.

The examples are in `PaymentsExamples`. A state is given as an object of the class that implements the service:

```scala
private val start = processor.holding(
  StreamProcessor(SpendLimits(BigInt(100), Nil), LedgerAccounts(Nil, Nil), OffsetCheckpoint(BigInt(0))))

example("a payment within the limit: approved, posted, the position past it"):
  val done = processor.handle(coffee).in(start)
  done.result && (processor.postingsOf("p1").in(done.after) is charged) &&
    (processor.position.in(done.after) is BigInt(1))
```

The Scala evaluator computes each of the eight on the code read from the classes, and Lean proves each from the
definitions printed from them.

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

The first checks the model is valid, that the examples hold of the code, and that the classes run as the Scala
they are. The second and third run Lean: every claim proven, every example held. The nodes are proposed, not
accepted: deciding them is the developer's, with their signing key.

## What this does not cover

- **State invariants as such.** A claim is said of the service in every state, so "no card is over its limit" is
  stated as what each call, and each step, keeps, not as a fact of every state.
- **The whole log as one theorem.** What is proven is the step: each call leaves its payment applied and moves the
  position only past it. "Every payment below the position is applied" follows by induction over the log, which
  rests on `deliveryIsAtLeastOnce` and is not carried out in Lean.
- **A step is a call of a held service.** That each such call is one transaction is the held service's to keep:
  a class over a database does it with a transaction, and the model does not check that it does.
- **One class for a trait.** A model gives one class for each service's trait, so a second implementation of
  `Accounts` cannot stand beside the first in this model; the first versions are traits of their own.
- **A class FrFlow cannot read.** `defineTested` for a service, a class tested against the claims, is not
  built; nor is the classes' Scala tested against the terms read from them on generated cases.
- **A member no claim mentions** has its code, and nothing is proven of it.
- **The breaking schedules are written by hand.** Lean proves or does not; nothing searches for the schedule.
- **One kind of event, one payment per call, a daily limit.** No refunds, no batches (the reader has no loops), no
  sliding window.
- **Liveness.** Nothing says a call finishes.
- **`IO`-style code.** The reader takes direct style; cats-effect values are invisible to the separation checker
  ([docs/SEPARATION-SPIKE.md](../../docs/SEPARATION-SPIKE.md)).
