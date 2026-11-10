# Wallet: a transfer service proven against retries and races

A wallet moves money between accounts. Three things go wrong in such a service in production, and each costs
money or a reconciliation:

- **A request sent twice is carried out twice.** A sender that hears nothing retries; a queue redelivers.
- **Two calls overdraw one account.** Each checks the balance, each sees enough, each pays.
- **Money is made or lost.** One side of a movement is written and the other is not.

None of them shows in a test that makes one call at a time. This example writes the service as ordinary Scala,
states what must hold as contracts in the companions of the classes, and has Lean prove the contracts of the code:
alone, and among other calls, whatever those do between its steps.

## The code

Plain Scala, direct style, no effect type and none of FrFlow's `Flow`. The service is what runs:

```scala
final class Transfers(ledger: Ledger^):
  def transfer(t: Transfer): Outcome =
    val mine = ledger.claim(t.request)
    if !mine then Outcome.Duplicate
    else
      val moved = ledger.moveIfCovered(t)
      if moved then Outcome.Done else Outcome.Refused
```

| File | What it holds |
| --- | --- |
| `Domain.scala` | `Posting`, `Books`, `Transfer` (contract: the amount is positive), `Outcome`; what is said of books: `balance`, `total`, `made`, `solvent`, `orderly` |
| `Ledger.scala` | The store: a `caps.Mutable` class, each method one transaction. Its companion holds its contracts |
| `Transfers.scala` | The service above. Its companion holds its contracts |
| `Hasty.scala` | The same service written check-then-act: the version with the race |
| `Others.scala` | What other calls may do between two steps of a call (`undisturbed`) |
| `Wallet.scala` | The model: which contract rests on which, and what is trusted |

The store and the services compile under Scala's capture and separation checking: the ledger is `Mutable`, a method
that changes it is an `update`, a service holds it exclusively (`Ledger^`). That is what lets FrFlow read a method
that changes the ledger as a function from the books to the books, with no state monad.

## The contracts, and what proves them

`updating { … }` reads a method as a function of the store's state: its answer with the state after.
`interleaving { … }(others)` reads it among other calls: before each step after the first, other calls may have
replaced the books, and the method's answer comes with every step it took. Each reading is attached to a
`Definition` the contracts speak of (`implementProven`), so the Lean definition is printed from the method's body.

The ledger's contracts are proven of its methods' bodies. The service's contracts are proven from the ledger's
contracts only: in Lean the service is a function of *any* `claim` and `moveIfCovered` that meet them. A ledger
kept in a database meets the same contracts or the proof does not apply; the service's proof does not change.

| Contract | Says | Proof |
| --- | --- | --- |
| `Ledger.claimKeepsPostings`, `claimIsWonOnce`, `claimedStaysClaimed`, `lostClaimChangesNothing` | What a claim does | automatic |
| `Ledger.moveIsMadeWhenCovered`, `moveKeepsTotal`, `moveKeepsClaims`, `movePostsItsRequest` | What a move does | automatic |
| `Ledger.moveKeepsSolvent` | A covered move overdraws nobody | by hand |
| `Transfers.neverOverdrawn` | No account is overdrawn at any step, whatever other calls do | automatic |
| `Transfers.moneyIsConserved` | No step makes or destroys money | automatic |
| `Transfers.carriedOutOnce` | No step adds postings to a request already made | by hand |
| `Transfers.leavesOthersUndisturbed` | Each step grants other requests what the service relies on | by hand |
| `Transfers.postsOnlyOnceClaimed` | A call that finds its request claimed posts nothing | by hand |
| `Transfers.coveredIsDone`, `sentAgainIsDuplicate` | What a caller is answered | automatic |
| `Transfers.sentAgainChangesNothing` | A retry changes nothing | by hand |

"Automatic" is FrFlow's own tactic; "by hand" is a proof file under `lean/Proofs/Wallet/`: seven of them over
shared lemmas (`Lemmas.lean`), and the examples' proofs (`Whole.lean`), about 340 lines of Lean in all. Lean checks
both kinds. No proof uses `sorry` or an axiom beyond Lean's standard three.

## How races are ruled out

The contracts among other calls quantify over a schedule: `between` maps a step's number to the books other calls
left before it. A schedule is admitted when it satisfies `undisturbed` for the call's request: the books are still
solvent and orderly, no claim was undone, and nobody else posted for this request. A contract proven for every
`between` holds for every interleaving in which the other calls behave that way.

That the other calls do behave that way is the second half, and it is proven of the service itself:
`leavesOthersUndisturbed` (each of its steps keeps `undisturbed` for every other request) and
`postsOnlyOnceClaimed` (a call of the same request that lost the claim posts nothing). The service relies on
others for exactly what it is proven to grant them.

Two statements are trusted and marked as design decisions in the model, for the developer to accept or reject:

- `ledgerIsTransactional`: each method of the ledger is one transaction. The proofs treat a method as one step.
- `othersLeaveARequestAlone`: every caller of the ledger is a service that meets those two contracts, and of two
  calls of one request one wins the claim. The last part follows from `claimIsWonOnce` once the ledger is
  transactional; it is argued in the node's text and is not a Lean theorem over two calls at once.

## The version with the race

`Hasty` reads whether the request is claimed and what the payer has, then marks and moves. Alone it is the same
service: its answer and the books it leaves agree with `Transfers` on 300 generated cases, and Lean proves it keeps
the books solvent (`hastyIsSafeAlone`). `neverOverdrawn` cannot be proven of it, and `WalletExamples` gives the
schedule that shows why: Alice holds 100 and pays Bob 80; between Hasty's check and its move another call pays
Carol 80 from the same account.

| On that schedule | Answer | Accounts |
| --- | --- | --- |
| `Hasty` | done | Alice at −60 |
| `Transfers` | refused | nobody overdrawn |

Both rows are examples of the model. The Scala evaluator computes them, and Lean proves each from the definitions
printed from the methods.

## Running it

```bash
sbt "testing/testOnly frflow.eval.WalletSuite"
```

```bash
sbt "project/Lean/testOnly frflow.project.WalletLeanSuite"
```

```bash
bin/frflow wallet check
```

The first checks the model is valid, that each method run as Scala agrees with the term read from it on generated
cases, and that the examples hold of the code. The second and third run Lean: every claim proven, every example
held. The nodes are proposed, not accepted: deciding them is the developer's, with their signing key.

## What this does not cover

- **A crash between the two steps.** A request claimed and never moved is answered `Duplicate` when sent again.
  What is proven is at most once, not exactly once; a job that completes or releases stale claims is not modelled.
- **Liveness.** Nothing says a call finishes, and there is no deadlock to speak of with one store.
- **One store.** A service over two stores, or a store with an adapter (SQL behind a trait), is not read yet; the
  ledger here is its own model.
- **Callers outside the model.** Another program writing the same tables is covered only by the two design nodes.
- **`IO`-style code.** The reader takes direct style; cats-effect values are invisible to the separation checker
  ([docs/SEPARATION-SPIKE.md](../../docs/SEPARATION-SPIKE.md)).
