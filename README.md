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
3. The final refinement is the program's code itself. At that level, it can be developed in one of two ways:
   - As plain Scala, which FrFlow tests with property-based testing on generated cases, whose shape and data are
     driven by the statements about it.
   - As code in FrFlow's monadic DSL, which compiles both to executable code and to a Lean model, which is then used
     in a strict proof.

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

## Example: booking meeting rooms

People book meeting rooms for a stretch of time, and a room holds one meeting at a time. Below is the core of the
example; the whole of it is in [`examples/rooms`](examples/rooms).

### The code

The domain, and when a room is free: a booking covers the moments from its start up to its end; two bookings are
apart when they are in different rooms or share no moment.

```scala
/** What the booking form sends and the table stores. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: List[Booking]) derives LeanType

/** A booking covers the moments from its start up to its end. */
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

/** Two bookings are apart when they are in different rooms or share no moment. */
val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

/** A room is free for a request when each of the bookings is apart from it. */
val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }
```

Bookings come from the booking form, which sends only bookings that end after they start. That is trusted, so it is
an assumption, stated with `always`: every value of the type that can occur. The roots state the purpose over
`Declaration`s: concepts known only by what the statements say of them. A statement holds in every state the service
reaches, and reads what changes, such as what is booked, in the current one.

```scala
val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(
  always[Booking](b => b.start < b.end))

val booked = Declaration[List[Booking]]("the bookings made, as the world stands")

val bookedAfter = Declaration[Booking => List[Booking]]("the bookings made once a request is handled")

val accepted = Declaration[Booking => Boolean]("whether a request is accepted")

val bookWhenFree = Node.claim("A request is booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) =>
    bookedAfter(request) === when(free(booked, request))(booked :+ request).otherwise(booked)))
  .assuming(bookingsEndAfterStart)

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => accepted(request) === free(booked, request)))
  .assuming(bookingsEndAfterStart)
```

Booking a request is a `Definition`: what the code provides. Its program reads the room's bookings from the table,
asks the calendar, and adds the booking if it is granted, in one transaction. The table's two operations are
`Definition`s too, given their meaning by a model of what it stores. Lean proves the program against its claims. A
program that can fail says so where it is declared (`Definition[Booking => Flow[Boolean]]("…").failsWith[StoreDown]`);
a claim about its run then covers the runs that fail too, its `result` an `Either[StoreDown, Boolean]`, and FrFlow
checks the error against what the code raises.

```scala
val book = Definition[Booking => Flow[Boolean]]("booking a request: whether it was booked")

val inRoom = Definition[String => Flow[RoomBookings]]("a room's bookings, as the SQLite table gives them")
val add = Definition[Booking => Flow[Unit]]("a booking added to the SQLite table")

object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first"):
  inRoom.means(room => state.get.map(stored => make[RoomBookings](room, stored.filter(b => b.room === room))))
  add.means(booking => state.update(stored => stored :+ booking))

val bookIfGranted = program { (request: Term[Booking]) =>
  (for
    held  <- inRoom(request.room)
    booked = granted(held, request)
    _     <- Flow.when(booked)(add(request))
  yield booked).atomically }
```

What the world outside does with the table is assumed, and so is what always holds of it: nothing but the code
changes it, it starts empty, and runs on it never interleave. A claim of `always` on the table's state is a rule
below the roots: Lean has it of every state a statement reads, and proves that every program writing the table keeps
it.

```scala
val nothingElseWrites = Node.assumption("Nothing but the booking code changes the table.")(
  storedBookings.onlyCodeChanges)

val startsEmpty = Node.assumption("The table starts empty.")(storedBookings.initially(stored => stored === Nil))

val oneAtATime = Node.assumption("Bookings are processed one at a time.")(storedBookings.atomic)

val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .refines(bookWhenFree, acceptWhenFree)
  .assuming(nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)
```

Claims say what each `Declaration` is in the code, as these do for `accepted` and `bookedAfter`: what `book` returns,
run in the current state, answers whether a request is accepted, and the table in the state the run leaves
(`book(request).after`) is what is booked once it is handled. A statement reading the state a run leaves names the
state each value is read in, `.current` for the one before the run.

```scala
val acceptedIsAnswered = Node.claim("A request is accepted exactly when booking it answers booked.")(
  forall((request: Term[Booking]) => accepted(request).current === book(request).result))
  .refines(acceptWhenFree)

val bookedAfterIsStored =
  Node.claim("What is booked once a request is handled is what the table holds after booking it.")(
    forall((request: Term[Booking]) => bookedAfter(request).current === storedBookings.in(book(request).after)))
  .refines(bookWhenFree)
```

The calendar decides whether a request is granted. It is plain Scala and is not proven: FrFlow tests it
automatically with property-based testing, on a thousand generated cases, against its claim `grantWhenNoOverlap`
below.

```scala
val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

final class Calendar(held: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byStart = held.bookings.sorted(using startOrder).toVector

  def grants(request: Booking): Boolean =
    val i = byStart.search(request)(using startOrder).insertionPoint
    val before = byStart.lift(i - 1)
    val after = byStart.lift(i)
    val endsInTime = before.forall(_.end <= request.start)
    val startsAfter = after.forall(_.start >= request.end)
    request.room != held.room || (endsInTime && startsAfter)
```

What booking needs from the calendar (it refines booking's claims, not shown), refined into a claim over start and
end times, which code can compare. Lean proves each step.

```scala
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === free(held.bookings, request)))
  .refines(storeWhenFree, answerWhenFree)
  .assuming(bookingsEndAfterStart)

/** Two bookings do not overlap when they are in different rooms or one ends by the time the other starts. */
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)
```

The FrModel lists the statements and attaches the code: booking's program to be proven, the calendar to be tested on
cases drawn from the generators given for the domain's types, and the SQLite table's Scala to be tested against its
model on generated runs.

```scala
val rooms = FrModel("Rooms")(bookWhenFree, acceptWhenFree, bookedIsStored, bookedAfterIsStored, acceptedIsAnswered,
  storeWhenFree, answerWhenFree, neverOverlap, grantWhenFree, bookingsOfTheRoom, roomBookingsApart, grantWhenNoOverlap,
  nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
  .implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))
  .withGenerator(roomNames.describedAs("Oak or Elm"))
  .withGenerator(requests.describedAs("requests for Oak or Elm that end after they start"))
  .withGenerator(roomBookings.describedAs("a room's bookings, laid end to end, some back to back"))
```

Examples are ordinary tests:

```scala
class GrantedExamples extends FrFlowExamples(rooms):
  example("back to back: granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true

  example("overlapping: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
```

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
  A request is booked exactly when its room is free for its whole time.

Decision
  to review: it changed
  not mechanical: its meaning moved
  …
```

```text
formula:
  (∀ (x : Booking), (∀ (x_1 : World), ((bookedAfter x x_1) = (if (Rooms.free (booked x_1) x) then ((booked x_1) ++ [x]) else (booked x_1)))))
  
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
| Declaration | `Declaration[A](means)` | a concept known only by what the statements say of it, such as `booked`; never called by code. It may change as the service runs; `d.isConstant`, as an assumption, says it does not |
| Definition | `Definition[A](means)`, or `define { … }` given its meaning on the spot | what the code provides, such as `book`, and must be given a meaning: a program or a `define` (proven in Lean), plain Scala (tested), a value, or, for an operation on a state, a `StateModel` saying what it does (its Scala tested against the model) or the assumptions about it alone (`op.assumed`) |

They use two quantifiers: `forall`, every possible value, and `always`, every value the code FrFlow covers can produce
(`always[T](x => …)`, of a type; `always(stored)(s => …)`, every state a model reaches). A statement holds in every
state the service reaches, the World, which it never names: `stored.current` is a model's state as it stands,
`p(x).result` what a run of a program from it returns, `p(x).after` the state it leaves, read with `stored.in(…)`.

A statement refines the statements it serves (`.refines`) and lists the assumptions it rests on (`.assuming`). A
statement can refine several others, and there can be several roots, so the statements form a directed acyclic graph.

## Proven, tested and assumed

The code at the bottom of the graph is in one of three states, and `status` reports which:

- **Proven** code is written in the DSL (a `program { … }` over a `Flow`, or a `define`), and Lean proves that it
  meets its claims.
- **Tested** code is plain Scala. It is tested against its claims with property-based testing on generated cases; an
  operation on a state is tested against its model on generated runs, two of its calls at once among them.
- **Assumed** code is known only by the assumptions about it, such as an outside system's search: Lean takes them as
  given, and its Scala is tested against them where a generated run can tell.

Everything above the code is proven from these, and Lean proves the statements consistent: some meaning of every
`Declaration` makes them all hold. Nothing is checked when the code runs: FrFlow is for testing before production and
for proofs. What is left to trust is the assumptions the developer accepted, FrFlow's translation of the model to Lean
(which the examples cross-check by running the same model as Scala), and, for tested code, the cases the tests reach.

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
bin/frflow rooms status              # an example: rooms, auth, keycloak, crm, sharing
```

`sbt "frflowInitAgent toy --as NAME"` creates one with the agent layer enabled. `sbt test` runs FrFlow's fast tests;
`sbt leanTest` runs the ones that run Lean end to end, the examples' among them.

## Examples

Each example is a project in `examples/<name>`: its statements and code in `src/main`, its examples in `src/test`,
its proofs by hand in `lean/Proofs`, and its command line in `app` (`bin/frflow <name> COMMAND`). None has a decision
yet: each starts with no ledger, for its developer to decide. FrFlow's own suites test them, each whole in its
`PortSuite` (`sbt "project/Lean/testOnly <name>.PortSuite"`), against what the library before the rebuild recorded
(`reference/`).

- `rooms` books meeting rooms: the example above.
- `auth` is access control by a table of grants, and the smallest example.
- `keycloak` has realms, sign-in, token introspection and sign-out over HTTP. Its sessions are proven to follow the
  history of requests, and its store's lookup is known only by what is assumed of it.
- `crm` is a multi-tenant CRM on SQLite with an HTTP API. Its expiry job is a program over the database, proven from
  the database's model.
- `sharing` shares documents, folders and teams between people, with expiring shares, invitations, a trash, access
  requests, notifications and an audit log. Time, failures and concurrency are modelled.

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
- [docs/redesign/](docs/redesign/ARCHITECTURE.md) is the design record of the library as it was rebuilt.
