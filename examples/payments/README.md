# Payments: a stream processor proven to apply each payment once

A consumer reads card payments from a log and, for each, checks the card's daily limit, posts the money, and
commits its position. Every team that has written one knows the three ways it goes wrong:

- **A crash loses a payment.** The position was committed before the payment was posted.
- **A redelivery charges twice.** The log delivers at least once, and the posting was not guarded.
- **Two instances take a card over its limit.** After a rebalance both run; each checks the limit, each approves.

None of them shows in a test that runs one call to its end. This example writes the consumer as ordinary Scala,
states what must hold as contracts in the companions of its classes, and has Lean prove them of the code. The log
itself is not implemented: that it delivers at least once, in order, is an assumption the model names.

## The code

Direct-style Scala, no effect type and none of FrFlow's `Flow`. This is the method that runs:

```scala
final class Processor(limits: Limits^, accounts: Accounts^, checkpoint: Checkpoint^):
  def handle(p: Payment): Boolean =
    val approved = limits.authorise(p)
    if approved then accounts.post(p)
    checkpoint.commit(p.offset)
    approved
```

| File | What it holds |
| --- | --- |
| `Domain.scala` | `Payment`, `Decision`, `Spending`, `Posting`, `Books`, `Pipeline`, and what is said of them: `spent`, `withinLimits`, `total`, `made`, `orderly`, `applied` |
| `SpendLog.scala`, `Ledger.scala`, `Offsets.scala` | The stores: `caps.Mutable` classes, each method one transaction. Their companions hold their contracts |
| `Limits.scala`, `Accounts.scala`, `Checkpoint.scala` | The services, each over its own store. Their companions hold their contracts |
| `Processor.scala` | The method above, over the three services. Its companion holds its contracts |
| `Eager.scala`, `Blind.scala`, `Hasty.scala` | Three first versions, each with one of the bugs |
| `Others.scala` | What other calls may do between two steps of a call (`undisturbed`) |
| `Payments.scala` | The model: which contract rests on which, and what is trusted |

Three decisions in the stores carry the design, and each is a line or two:

- `SpendLog.assess` checks the limit and records the decision in one transaction, and leaves a payment already
  decided as it was.
- `Ledger.postOnce` posts and marks the payment in one transaction, and does nothing if it is marked.
- `Offsets.advance` is a compare-and-set: it moves the position only from the payment's offset to one past it.

## The contracts, and what proves them

`updating { … }` reads a method as a function of the stores' state: its answer with the state after.
`interleaving { … }(others)` reads it among other calls: before each step after the first, other calls may have
replaced the state, and the answer comes with every step taken. Each reading is attached to a `Definition` the
contracts speak of, so the Lean definition is printed from the method's body.

The tree has three levels. The stores' contracts are proven of their methods' bodies. The services' contracts
are proven from the stores'. The processor's are proven from the services' when it runs alone, and from the
stores' when it runs among other calls: in Lean it is a function of *any* `authorise`, `post` and `commit` that
meet their contracts.

| Contract | Says | Proof |
| --- | --- | --- |
| `Processor.handledIsApplied` | A payment handled is decided, and posted if approved, from any state | by hand |
| `Processor.positionMovesPastTheHandled` | Handling the payment the position is at moves it one past | automatic |
| `Processor.redeliveryChangesNothing` | Handled again, a payment gets the answer it got and changes nothing | automatic |
| `Processor.fittingIsApproved` | A new payment that fits the limit is approved | automatic |
| `Processor.neverOverTheLimit` | No card is over its limit at any step, whatever other calls do | by hand |
| `Processor.moneyIsConserved` | No step makes or destroys money | by hand |
| `Processor.postedOnce` | No step adds postings to a payment that has some | by hand |
| `Processor.neverCommitsAhead` | Only the last step moves the position, and only past a payment applied | by hand |
| `Processor.leavesOthersUndisturbed` | Each step grants other calls what the processor relies on of them | by hand |
| `Limits`, `Accounts`, `Checkpoint` (7) | Each service's answer is what is recorded; each call can be repeated | automatic |
| `SpendLog`, `Ledger`, `Offsets` (13) | What each transaction keeps and changes | 12 automatic, 1 by hand |

"Automatic" is FrFlow's own tactic; "by hand" is a proof file under `lean/Proofs/Payments/`. With the five
contracts of the first versions below that makes 34 claims, 25 automatic and 9 by hand, in about 360 lines of
Lean. Lean checks both kinds; no proof uses `sorry` or an axiom beyond Lean's standard three.

## How redelivery, a crash and a second instance are covered

- **Redelivery** is the method called again. `redeliveryChangesNothing` says the second call returns what the
  first did and leaves the state as it was.
- **A crash** is the call stopping after any of its steps. The contracts among other calls hold of every step,
  so they hold wherever it stops: in particular `neverCommitsAhead` says the position is never past a payment
  that is not applied. Recovery is redelivery from the state the crash left, and `handledIsApplied` holds from
  any state.
- **A second instance** is other calls between this call's steps. Those contracts quantify over a schedule:
  `between` maps a step's number to the state other calls left before it, admitted when it satisfies
  `undisturbed`. That other instances do behave that way is proven of the processor itself
  (`leavesOthersUndisturbed`), for every payment, the one being handled included.

Three statements are trusted and marked as design decisions in the model, for the developer to accept or reject:

- `deliveryIsAtLeastOnce`: the log delivers every payment, in order from the committed position, and again
  after a restart.
- `storesAreTransactional`: each method of a store is one transaction.
- `othersKeepTheContracts`: every other caller of the stores is a processor, or keeps what it is proven to keep.

## The three first versions

Each is a few lines away from the processor, does one thing provably right, and passes any test of one call run
to its end.

| Version | The difference | Proven of it | What an example shows | Cannot be proven of it |
| --- | --- | --- | --- | --- |
| `Eager` | Commits first | Alone it answers and ends exactly as `Processor` | Stopped after its first step, the position is past a payment never applied | `neverCommitsAhead` |
| `Blind` | Posts without checking the mark | A payment handled is applied | Delivered again, the card is charged twice | `redeliveryChangesNothing`, `postedOnce` |
| `Hasty` | Checks the limit, then records | Alone it keeps every card within its limit | Another payment approved between its two steps, the card is over its limit | `neverOverTheLimit` |

The examples are in `PaymentsExamples`. The Scala evaluator computes each, and Lean proves each from the
definitions printed from the methods.

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

The first checks the model is valid, that each method run as Scala agrees with the term read from it on
generated cases, and that the examples hold of the code. The second and third run Lean: every claim proven,
every example held. The nodes are proposed, not accepted: deciding them is the developer's, with their signing
key.

## What this does not cover

- **The whole log as one theorem.** What is proven is the step: each call leaves its payment applied and moves
  the position only past it. "Every payment below the position is applied" follows by induction over the log,
  which rests on `deliveryIsAtLeastOnce` and is not carried out in Lean.
- **One kind of event.** Payments that charge a card. No captures or refunds.
- **A daily limit.** The day a payment counts toward is on the event; there is no sliding window.
- **One payment per call.** The reader has no loops, so a batch is not read; the method handles one delivery.
- **The breaking schedules are written by hand.** Lean proves or does not; nothing searches for the schedule.
- **`Payment`'s own contract** (a positive amount) is on the type and shapes the generated test cases. No proof
  needs it, so no node states it.
- **Liveness.** Nothing says a call finishes.
- **`IO`-style code.** The reader takes direct style; cats-effect values are invisible to the separation checker
  ([docs/SEPARATION-SPIKE.md](../../docs/SEPARATION-SPIKE.md)).
