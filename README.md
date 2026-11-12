# FrFlow

FrFlow is a Scala 3 library for building software together with a formal model of it, proven in Lean 4.

## The opportunity and the problem with agentic coding

Coding with agentic AI has massively changed software engineering. By using it, developers can explore the solution
space much faster, and build products at much higher velocity.

However, the massive volume of generated code and the nature of agentic coding introduce new challenges. This library,
inspired by the *Future of Programming* talk (Nada Amin, Scala Days 2026), identifies two core issues that introduce
significant risk and cost to the new, agentic software engineering process. Namely:

1. **Lost theory.** Peter Naur argued that a program is the visible part of a theory its programmers hold: why it is
   built the way it is, and how it maps to the world. When agents write the code, nobody on the team builds that
   theory. The agent loses it too, when its context ends. A system nobody understands cannot be changed safely.

2. **Increasing entropy.** A codebase that grows in size without proper tracking of its content and architecture
   suffers from a lack of integrity, which may eventually cause inconsistencies, and even fundamental bugs or security
   vulnerabilities.

## Proposed solution

FrFlow proposes a way to build a formal, logically proven model of the developed software as a refinement graph. It
follows the method of stepwise refinement (Wirth, 1971) and the refinement calculus (Back, 1978; Morgan, 1990):

1. Development starts from a specification: a small set of core, formal statements about the program.
2. Then, gradually, each statement is refined. A refinement step replaces a statement with more concrete statements
   that together imply it. Every refinement step is a proof obligation, and Lean checks it, so a statement can never
   contradict the one it refines, and Lean also proves that the statements as a whole do not contradict each other.
3. The final refinement is the program's code itself. Its specification is declared on the code's own
   interfaces: a service is a trait, a `Declaration` of the trait is the value the claims speak of, and the claims
   are written through the trait's members. An implementation is then one of:
   - **Lifted**: a class that implements the trait, written as ordinary Scala. FrFlow compiles the class into the
     model from the TASTy the Scala compiler wrote for it, and the prover shows that it meets every claim, alone
     and among other calls ([docs/LIFTED.md](docs/LIFTED.md);
     [examples/payments](examples/payments/README.md): a stream handler proven to apply each payment once, through
     redelivery, a crash at any step and a second instance).
   - **Assumed**: no implementation is given. The trait is known by the assumptions about it, as an outside
     system or a library is.
   - **Tested**: plain Scala, which FrFlow tests with property-based testing on generated cases, whose shape and
     data are driven by the statements about it.
   - Code in FrFlow's monadic DSL, which compiles both to executable code and to a model used in a strict proof.

The logical model sits alongside the code that performs the given functions, and acts as its contract: an interface
the code conforms to, albeit stricter and more powerful than has been usual for software.

Normally, developing formal proofs for the functions of software would be a costly and inefficient way to verify and
define software. However, with coding agents, this approach of thorough formal software verification has become viable
and should be explored.

## How FrFlow addresses problems of agentic coding

In essence, FrFlow makes sure that there is a view of the software that is correct by construction. The refinement
graph is the source of truth, and it is meant to be impossible to diverge from at the functional level.

Every refinement step is proven in Lean, from the statements about a single function up to the core statements at the
root. When the code meets them, the core statements hold as well. Nobody has to take it on trust that a check
somewhere deep in the code really gives the property stated at the top.

This addresses both problems. The graph, with the reason each statement was accepted for, signed in its decision, is
the theory of the program, and it stays in the repository after the agent's context ends. And every change to the code
or to a statement brings the statements it affects back to the developer for review, with the diff, so the codebase
cannot drift away from its specification unnoticed.

**That makes it possible for a human developer to realistically take responsibility and sign off on mission-critical
software, even if its parts are developed by agentic AI.**

The value of FrFlow is not limited to agentic coding, and it does not need to be used with AI. I encourage the exercise
of building software with this approach, as it makes it much easier to achieve confidence about the quality of the
developed software.

## Example: handling card payments

A consumer reads card payments from a log and, for each, checks the card's daily limit, posts the money and commits
its offset. Below is the core of the example; the whole of it is in [`examples/payments`](examples/payments/README.md).

### The code

An id is a type of its own over a string, so one is never given where another is meant:

```scala
opaque type PaymentId = String
object PaymentId extends FrSpec.Opaque[PaymentId, String]
```

A service is an ordinary trait, with the members such a service has and nothing added for the proofs. Its
specification is in its companion: a `Declaration` of the trait, which is the value the claims speak of, and the
claims, written through the trait's members.

```scala
/** The consumer's offsets in the log: the committed offset is that of the next payment to handle. */
trait ConsumerOffsets extends Mutable:
  /** Commits a payment's offset: the committed offset moves one past it, if it is at it. */
  update def commit(offset: BigInt): Unit
  /** The offset of the next payment to handle: every payment before it has been handled. */
  def committed: BigInt

object ConsumerOffsets:
  val offsets = Declaration[ConsumerOffsets]("the consumer's offsets: the offset of the next payment to handle")

  val commitMovesPast = Node.claim("Committing the offset that is committed moves it one past.")(
    forall((offset: Term[BigInt]) =>
      (offsets.committed === offset) implies
        (offsets.committed.in(offsets.commit(offset).after) === offset + 1)))

  val commitElsewhereChangesNothing = Node.claim("Committing any other offset changes nothing.")(
    forall((offset: Term[BigInt]) =>
      (offsets.committed =!= offset) implies (offsets.commit(offset).after === offsets.current)))
```

An implementation is a class, as it would be written without FrFlow:

```scala
final class CommittedOffset(var committed: BigInt) extends ConsumerOffsets:
  update def commit(offset: BigInt): Unit =
    if committed == offset then committed = offset + BigInt(1)
```

The handler has one method and holds three services. Its claims are said through the interfaces of what it holds
(`ledger.total`, as the handler has the ledger after the call), so no trait has a member for a proof's sake:

```scala
trait PaymentHandler extends Mutable:
  /** Handles one payment: has it authorised, posts it if it is approved, and commits its offset. */
  update def handle(payment: Payment): Boolean

object PaymentHandler:
  val handler = Declaration[PaymentHandler]("the payment handler: it handles one payment from the log")

  val moneyIsConserved = Node.claim("Handling a payment makes no money and destroys none.")(
    forall((p: Term[Payment]) => ledger.total.in(handler.handle(p).after) === ledger.total))

  val redeliveryChangesNothing = Node.claim("A payment handled again gets the answer it got and changes " +
      "nothing.")(
    forall((p: Term[Payment]) =>
      (handler.handle(p).in(handler.handle(p).after).result === handler.handle(p).result) &&
        (handler.handle(p).in(handler.handle(p).after).after === handler.handle(p).after)))

  // Every step of the call, whatever other calls do between the steps: a second instance after a rebalance.
  val noStepMakesMoney = Node.claim("No step of handling a payment makes money or destroys it.")(
    forall((p: Term[Payment]) =>
      handler.handle(p).amongOthers(run => run.steps.forall(step =>
        ledger.total.in(step._2) === ledger.total.in(step._1)))))

final class StreamPaymentHandler(limits: CardLimits^, ledger: Ledger^, offsets: ConsumerOffsets^)
    extends PaymentHandler:
  update def handle(payment: Payment): Boolean =
    val approved = limits.authorise(payment)
    if approved then ledger.post(payment)
    offsets.commit(payment.offset)
    approved
```

The model lists the claims, which claim refines which, and the class given for each trait:

```scala
val payments: FrModel = FrModel("Payments")(
  PaymentHandler.moneyIsConserved, PaymentHandler.redeliveryChangesNothing, PaymentHandler.noStepMakesMoney, // …
  Ledger.postKeepsTotal.refines(PaymentHandler.moneyIsConserved, PaymentHandler.noStepMakesMoney),
  ConsumerOffsets.commitMovesPast.refines(PaymentHandler.redeliveryChangesNothing), // …
  offsets.define(lifted[CommittedOffset]),
  handler.define(lifted[StreamPaymentHandler](limits, ledger, offsets)))
```

The examples state facts of the code at work, on objects of the classes:

```scala
class PaymentsExamples extends FrFlowExamples(payments):
  private val start = handler.holding(
    StreamPaymentHandler(RecordedLimits(BigInt(100), Nil), PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))

  example("a payment within the limit: approved, posted, its offset committed"):
    val done = handler.handle(coffee).in(start)
    done.result && (ledger.postingsOf(p1).in(done.after) is charged) &&
      (offsets.committed.in(done.after) is BigInt(1))
```

### From a class to a proof

`lifted[CommittedOffset]` is an ordinary call that runs when the model is built. It is a compiler, with no macro
and no second Scala compilation in it:

1. The Scala compiler writes, beside each class file, a `.tasty` file: the class as it was typed, bodies included.
2. FrFlow opens that file, walks each member's tree and builds the member's term: a function of the class's state
   (a record of its constructor's fields) and the member's inputs, which gives its result and, of an `update`
   member, the state after it. Scala it does not read is refused, with the file and line.
3. The prover's printer prints each term as a definition, and the prover shows it meets each claim that names the
   member.

A class that holds services is proven from the claims on them, not from their classes: `handle` is a function of
any card limits, ledger and offsets that meet their claims. That is what `.refines` says in the model, and why a
service can be replaced by another that meets the same claims. Each `update` member is also compiled as its steps
among other calls (`amongOthers`): before each step but the first, the others may have left any state.

Of the example's 29 claims, Lean proves 26 by FrFlow's tactic and 3 from proofs by hand, and all 8 examples. Rocq
proves 27 by the tactic and 2 by hand ([docs/ROCQ.md](docs/ROCQ.md)).

## Decisions at work: booking meeting rooms

A model is decided and kept the same way whatever it is about. [`examples/rooms`](examples/rooms) is the one whose
decisions FrFlow's suites replay: people book meeting rooms for a stretch of time, and a room holds one meeting at
a time. It is written with `define`, a `program` over a store and a calendar in plain Scala that is tested.

### How it works

`bin/frflow rooms check` proves the steps in Lean, tests the calendar against `grantWhenNoOverlap` and the table's
Scala against its model on generated cases, and has Lean prove that a meaning exists for the `Declaration`s under which
every statement holds. Once the developer has accepted every node (`bin/frflow rooms review`), it ends:

```text
Consistency: a meaning for what is open under which every statement holds
  bookedIsStored: proven
    booked: as bookedIsStored defines it
  bookedAfterIsStored, acceptedIsAnswered, grantWhenNoOverlap: proven
    granted: as grantWhenNoOverlap defines it
    bookedAfter: as bookedAfterIsStored defines it
    accepted: as acceptedIsAnswered defines it

FrModel: 16 nodes, 16 accepted
Code: 4 proven, 3 tested; consistency proven
Examples: 2/2 pass
Nothing waits: every node is accepted and proven, or its code tested.
```

### How changes cause failures

The calendar forgets the booking after the request. Property-based testing finds a case that fails:

```diff
     val before = byStart.lift(i - 1)
-    val after = byStart.lift(i)
     val endsInTime = before.forall(_.end <= request.start)
-    val startsAfter = after.forall(_.start >= request.end)
-    request.room != held.room || (endsInTime && startsAfter)
+    request.room != held.room || endsInTime
```

```text
x grantWhenNoOverlap: fails a generated case: (("Elm", List(("Elm", 0, 5))), ("Elm", 0, 1)): its result breaks the claim (seed 1, case 11, size 1)
```

An agent takes meetings that touch to overlap, and changes the claim over times, the calendar and the examples to
match. The calendar's tests pass, but Lean refutes the step to `grantWhenFree` with a case it confirms, and the lemmas
over the same times no longer build, so the rules resting on them stay open:

```diff
 val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
-  a.room =!= b.room || a.end <= b.start || b.end <= a.start }
+  a.room =!= b.room || a.end < b.start || b.end < a.start }
```

```text
x grantWhenFree: failed
  complete: open
  …
  a step is refuted on: held = ("Elm", List(("Elm", 0, 3))), request = ("Elm", 3, 5)
```

The agent also changes `covers` to include the end. Now everything agrees with the misreading and every proof passes,
but the change reaches every claim, so all 12 go back to the developer. `bin/frflow rooms review` shows each, and
`bin/frflow rooms diff bookWhenFree` what changed:

```diff
-val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }
+val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t <= b.end }
```

```text
! bookWhenFree  claim (a root)  to review
  Once a request is handled, the bookings are those before it, with the request added if its room is free for its whole time.

Decision
  to review: it changed
  not mechanical: its meaning moved
  …
```

```text
formula:
  (∀ (x : Booking), (∀ (x_1 : World), ((bookedAfter x x_1) = (Rooms.addedIfFree (booked x_1) x))))
  
  ...
  
  @[frflow_defs] def covers (x : Booking) (x_1 : Int) : Prop :=
-   ((x.start ≤ x_1) ∧ (x_1 < x.«end»))
+   ((x.start ≤ x_1) ∧ (x_1 ≤ x.«end»))
```

Only the developer's signed decisions count, so an agent cannot accept the change. `WalkthroughSuite` replays these
three changes and compares what `check`, `status`, `review` and `diff` print with the text above
(`sbt "cli/Lean/testOnly rooms.walkthrough.WalkthroughSuite"`).

## Statements

There are three kinds of statements, the nodes of the graph:

| Kind | Written | What it says | How it is checked |
|---|---|---|---|
| claim | `Node.claim(statement)(formula)` | a property of the system, in the words of its domain | Lean proves it from the claims that refine it, or of the code it mentions; where that code is plain Scala, it is tested on generated cases |
| assumption | `Node.assumption(statement)(formula)` | what is trusted: the world outside the code, an outside system's promise, what comes from outside | decided by the developer; what Lean takes as given, and plain Scala it is about is tested against it where it can be |
| design | `Node.design(statement)(files*)` | an architecture decision no proof covers | decided by the developer; a change to the files it governs brings it back |

Statements are about two kinds of values:

| Value | Written | What it is |
|---|---|---|
| Declaration | `Declaration[A](means)` | a word of the model: what statements speak of and code calls. One nothing defines is known only by what the statements say of it, such as `booked`; if only statements read it, it may change as the service runs (`d.isConstant`, as an assumption, says it does not) |
| Structure | `Declaration[Trait](means)`, of a trait of the developer's | a value with members: a service, a store. Its members are called on terms as the trait declares them: `limits.authorise(p).result` is what the call gives, `.after` the structure after it, `.in(state)` the same from a given state, `limits.current` the structure as it stands, `.amongOthers(run => …)` every step of the call among other calls. A claim on a class that holds it asks it as the holder has it: `ledger.total.in(handler.handle(p).after)` |
| Definition | `d.define(…)` of a Declaration, listed in the model beside the nodes; or `define { … }`, declared and defined at once | a Declaration with a meaning, such as `book`: a class that implements a structure's trait (`d.define(lifted[Class])`, compiled from its TASTy and proven), a program or a `define` (`d.define`, proven), plain Scala (`d.defineTested`, tested), a value (`d.defineValue`, `d.provided`), or, for an operation on a state, a `StateModel` saying what it does (its Scala, `defineOperations`, tested against the model) or the assumptions about it alone (`op.assumed`) |

They use two quantifiers: `forall`, every possible value, and `always`, every value the code FrFlow covers can produce
(`always[T](x => …)`, of a type; `always(stored)(s => …)`, every state a model reaches). A statement holds in every
state the service reaches, the World, which it never names: `stored.current` is a model's state as it stands,
`p(x).result` what a run of a program from it returns, `p(x).after` the state it leaves, read with `stored.in(…)`.

A statement refines the statements it serves (`.refines`) and lists the assumptions it rests on (`.assuming`). A
statement can refine several others, and there can be several roots, so the statements form a directed acyclic graph.

## Proven, tested and assumed

The code at the bottom of the graph is in one of three states, and `status` reports which:

- **Proven** code is one of three things. A class that implements a structure's trait, lifted by its type
  (`limits.define(lifted[RecordedLimits])`): it is compiled from its TASTy as the model is built, and each member is
  proven to meet every claim on it, alone and among other calls. A function of plain Scala that has no state, no
  effect and cannot fail, read at compile time (`lifted { (a: Booking, b: Booking) => … }`); `testing.Agreement`
  tests its Scala against its term on generated cases. Or code in the DSL (a `program { … }` over a `Flow`, or a
  `define`). [docs/LIFTED.md](docs/LIFTED.md) lists the Scala that is read.
- **Tested** code is plain Scala. It is tested against its claims with property-based testing on generated cases; an
  operation on a state is tested against its model on generated runs, two of its calls at once among them.
- **Assumed** code is known only by the assumptions about it, such as an outside system's search: Lean takes them as
  given, and its Scala is tested against them where a generated run can tell. A structure with no class is known
  the same way (`pricing.provided`); a model that holds one is valid, and the prover does not build it yet.

Everything above the code is proven from these, and Lean proves the statements consistent: some meaning of every
`Declaration` makes them all hold. Nothing is checked when the code runs: FrFlow is for testing before production and
for proofs. What is left to trust is the assumptions the developer accepted, FrFlow's translation of the model to Lean
(which the examples cross-check by running the same model as Scala), and, for tested code, the cases the tests reach.

Lean 4 is the prover that checks a project (`check`). FrFlow is moving to Rocq: the payments and auth examples are
printed as Rocq from the same generated modules and proven by Rocq 9 (`sbt rocqTest`); the other examples stay on
Lean until they are moved ([docs/ROCQ.md](docs/ROCQ.md)).

Time is modelled as Cats Effect models it: the clock is a model of FrFlow's own (`Clock.now`, `Clock.sleep`), steps of
code take no time of their own, and the world moves the time on between runs and at each of the clock's steps.
FrFlow states safety properties: "eventually", and two runs in sequence in one statement, are out of scope for now.

## Decisions

The developer accepts or rejects every statement, in the terminal or in a local web view. Each decision is signed with
the developer's key and kept in a ledger in the repository, and counts only when its key is on the project's list of
deciders, which the developer signs. When anything a decision rests on changes, the statement comes back for review
with the diff. `status` exits with 1 while anything waits for a decision or is not proven, so CI can gate on it.

## Using it

`bin/frflow PROJECT COMMAND` runs the command line of a project, on the terminal with colors and the interactive
review; `sbt "PROJECT/run COMMAND"` gives the same, plain.

- `tree` shows the graph from the roots, with each statement's mark, kind and state.
- `show NODE` shows one statement: what it says and why it was accepted, its formula, how it is checked, where it
  sits, its parts and the rules it uses, and what Lean proved; `diff NODE` what moved since it was decided.
- `review` goes through the statements waiting for a decision, each with what changed; `inbox` lists them.
- `check` renders the model as Lean, proves it and tests the code; `status` shows the state of the whole project, and
  `ci` does both for CI.

`sbt "PROJECT/serve --as NAME"` runs the same as a local web view, with the graph, the statement under review and its
diff, and the inbox. Decisions are signed the same way as in the terminal.

## With an AI agent

The agent layer (`modules/agent`) is enabled per project with `extensions = List(frflow.agent.Agent)`. The developer
describes the idea to the agent, which asks what it needs to know, proposes a README and the roots and their
refinements, writes the proofs and the code, and answers the developer's requests about any statement. The decisions
stay with the developer. The agent's rules are in [`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

## Getting started

You need JDK 17 or later, sbt, and Lean 4.35.0 installed with [elan](https://github.com/leanprover/elan), so that
`lake` is on the `PATH`.

```sh
git clone https://github.com/szymon-rd/fr-flow && cd fr-flow
sbt "frflowInit toy --as NAME"       # an empty project in examples/toy, NAME its first decider
sbt reload
bin/frflow toy status                # compiles on first use
sbt "toy/serve --as NAME"            # the web view on localhost, deciding as NAME
bin/frflow rooms status              # an example: rooms, auth, payments, shop
```

`sbt "frflowInitAgent toy --as NAME"` creates one with the agent layer enabled. `sbt test` runs FrFlow's fast tests;
`sbt leanTest` runs the ones that run Lean end to end, the examples' among them; `sbt rocqTest` runs the ones that
run Rocq (payments and auth), and needs Rocq 9 with `rocq` on the `PATH` (`opam install rocq-prover`).

## Examples

Each example is a project in `examples/<name>`: its statements and code in `src/main`, its examples in `src/test`,
its proofs by hand in `lean/Proofs` (and `rocq/Proofs`, where it is proven in Rocq), and its command line in `app`
(`bin/frflow <name> COMMAND`). None has a decision yet: each starts with no ledger, for its developer to decide.
FrFlow's own suites test them whole (`sbt leanTest`, `sbt rocqTest`).

- `payments` is the example above: a payment stream handler over three services, each a structure, proven
  through redelivery, a crash at any step and a second instance, in Lean and in Rocq.
- `rooms` books meeting rooms: the decisions shown above.
- `auth` is access control by a table of grants, and the smallest example; proven in Lean and in Rocq.
- `shop` is a checkout over two services and a store, proven among other calls in the shape before structures,
  a word per method (`updating`, `interleaving`).

## References

- Nada Amin, [*Future of Programming*](https://scaladays.org/session/future-of-programming/), keynote at Scala Days
  2026.
- Peter Naur, *Programming as Theory Building* (1985).
- Niklaus Wirth, *Program Development by Stepwise Refinement*, Communications of the ACM 14(4), 1971.
- Ralph-Johan Back, *On the Correctness of Refinement Steps in Program Development*, PhD thesis, University of
  Helsinki, 1978; and Ralph-Johan Back and Joakim von Wright, *Refinement Calculus: A Systematic Introduction* (1998).
- Carroll Morgan, *Programming from Specifications* (1990).
- Eric Evans, *Domain-Driven Design* (2003).
- Leonardo de Moura and Sebastian Ullrich, *The Lean 4 Theorem Prover and Programming Language* (2021).

## Documentation

- [docs/index.html](docs/index.html) has a tutorial, how-to guides, the reference and troubleshooting.
- [docs/USAGE.md](docs/USAGE.md) describes the DSL, the commands, their output and exit codes, what Lean proves, the
  warnings, the web view and the modules.
- [docs/DAG.md](docs/DAG.md) describes the design of the refinement graph.
- [docs/LIFTED.md](docs/LIFTED.md) describes plain Scala compiled into the model (`lifted`, `FrSpec`, structures):
  what is read, how the Scala, the term and the prover's definition are held to one meaning, and what is not built
  yet.
- [docs/ROCQ.md](docs/ROCQ.md) describes the move from Lean to Rocq: how a model reads in Rocq, what is proven
  there, and what is left.
- [docs/redesign/](docs/redesign/ARCHITECTURE.md) is the design record of the library as it was rebuilt, and the
  owner's decisions the sources cite.
