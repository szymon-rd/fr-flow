# Threads: could FrFlow prove Ox's threading model?

An analysis, on top of [LIFTED.md](LIFTED.md) and [ROCQ.md](ROCQ.md). It asks whether the threading model of
[Ox](https://github.com/softwaremill/ox) (structured concurrency in direct style, on Java's virtual threads) could
be proven correct by claims of a new kind, what those claims are, what must be assumed of Java's threads, and
which operators a claim needs.

What was done: the sources of Ox's core were read (`com.softwaremill.ox:core_3:1.1.0`, from its sources jar: scopes,
forks, the supervisor, the thread set, `par`, `race`, `uninterruptible`, fork locals), and the argument that a
scope's forks have finished when it completes was modelled and proven in Rocq with its standard library
([threads/Herd.v](threads/Herd.v)), as was the argument that a closing scope completes
([threads/Closing.v](threads/Closing.v)). Nothing was built in FrFlow. Ox was read; later two of the findings
were run (below). Iris is not installed on the machine this was written on ("Where it stands" at the end).

The short answer: yes for safety, in two layers. The protocol inside a scope is a state machine whose invariant
FrFlow's `always` nearly states already, and a first-order proof of it works today (`Herd.v`). The rule Ox's users
rely on (what forks are lent comes back when the scope completes) is a statement of ownership over any body, which
needs separation logic: Iris. Liveness ("a closing scope completes") needs no Iris and is not helped by it: over
Ox compiled to steps it is a rank and an assumption of fairness in plain Rocq (`Closing.v`), with assumptions
about the forks' bodies and the scheduler that are stronger than those of safety.

## The proof on Ox's code

Since this page was first written, containment has been proven of Ox's scope and fork code itself, not of a
model: [examples/ox/rocq/Ox/README.md](../examples/ox/rocq/Ox/README.md) says what is proven, what is assumed
and what is not. In short:

- **The design is the one this page proposes.** The JDK's classes are contracts taken as assumptions
  (`modules/proof/rocq/FrFlow/Threads/Jdk.v`: a state per class, a contract per method). Ox's methods are
  programs that call them (`examples/ox/rocq/Ox/Gen.v`). Each method gets a claim proven from the contracts and
  from the claims on the methods it calls, and the theorem is proven from those.
- **The theorem** (`Main.contained`, no axioms): for every client that forks into a scope only closures holding
  capabilities of that scope or of scopes enclosing it, once the first thread has ended no thread has an
  operation left, by every order of the threads' steps, at any nesting of scopes. `Example.example_contained` is
  the same for one client with nothing assumed of it.
- **It is plain Rocq.** The rules of proof are an invariant with ghost state and a rely, proven sound once
  (`Logic.v`, 200 lines). Framing, which separation logic gives for nothing, is done by a syntactic class of
  programs that touch nothing the invariant reads; a tactic finds that the supervisor, the error mode and the
  futures are in it.
- **The code is read, not transcribed.** `examples/ox/rocq/Ox/Gen.v`, which the proofs import, is generated
  from the TASTy in Ox's published jar ([THREADS-GENERATOR.md](THREADS-GENERATOR.md)). A translation by hand
  made first (`Code.v`) is the same text, and `Agree.v` proves the two equal definition by definition.
- **What the proof found, beyond the reading below**: lexical scoping does not confine a capability
  (`fork(using outer) { fork(using inner) { … } }` type-checks and passes Ox's run-time check), so the
  condition on the client is about what a forked closure holds, not about where it is written.

Two findings of this page were then run against Ox 1.1.0 itself (`examples/ox/probe`): the leak through a
capability handed to a fork of an enclosing scope occurred in 7 and 21 of 200,000 rounds, and a `join` on a
cancelled fork from outside its scope was still blocked after 5 seconds. A third was found on the way and
run: `forkUser` counts a fork before `startThread` can refuse it, so a refused user fork leaves a supervised
scope waiting for ever. The other two findings (`isEmpty`, an
interrupt before `start`) are still of the reading only.

The three models in `docs/threads/` stay as they were: `Herd.v` is superseded for containment by the proof on
the code; `Closing.v` (liveness) and `Wakeup.v` (no lost wake-up) are still models only.

## Ox's shape

- **A scope** (`supervised`, `supervisedError`, `unsupervised`) is a capability (`Ox`, given to the body as a
  context parameter) holding a thread set (`ThreadHerd`: a concurrent set `threads`, a flag `shutdownInProgress`,
  the owner thread), a supervisor (a counter of user forks running, a `CompletableFuture` for the first outcome,
  two sets for the later ones), a list of finalizers in an `AtomicReference`, its parent, and its fork locals. The
  thread's current scope is a `ThreadLocal`.
- **A fork** is a thread of the scope's set: `startThread` checks the flag, checks the caller is in some scope,
  makes the thread, adds it to the set, starts it; the thread takes itself out of the set in a `finally`. `fork`
  (daemon) and `forkUser` report an exception to the supervisor; `forkUser` is counted; `forkUnsupervised` reports
  nothing. A fork's result is a `CompletableFuture` that `join` reads.
- **A scope ending.** `supervised` runs its body as a user fork and blocks on the supervisor's future, which
  completes when the count of user forks reaches zero or at the first failure. Then, in a `finally`,
  `interruptAllAndJoinUntilCompleted` sets the flag and loops while the set is not empty, interrupting each thread
  once and joining each. Then the finalizers run, once, uninterruptibly.
- **The rest is written with these**: `par` is a `supervised` with a fork per branch, `race` an `unsupervised` with
  a queue, `timeout` a race with a sleep, `uninterruptible` a fork joined in a loop, a cancellable fork a nested
  scope. Channels are another library's (jox).

So the threading model is small: one protocol (the set, the flag, the closing loop), one supervisor, and a list of
finalizers, over about ten classes of the JDK.

## 1. What claim counts as a proof that a threading library is correct

Three kinds of claim are accepted, for three kinds of library:

| Kind | Claim | Used for |
|---|---|---|
| A specification per operation in a concurrent separation logic, with the logic's adequacy theorem | every program proven against the specifications is safe: no step goes wrong, no data race, and its result meets its postcondition | thread primitives and locks: Iris's `spawn`, `join` and `par`; RustBelt's `thread::spawn` and `rayon::join` |
| Linearizability, or refinement of an atomic model | every run of the code among any other threads is a run of a model in which each operation takes one step | concurrent data structures: queues, channels, semaphores (CQS, the framework behind Kotlin coroutines' semaphore and mutex, proven in Iris) |
| An inductive invariant of a model of the protocol | no reachable state of the model is bad | protocols, in TLA+ and the like; the code is not what is proven |

For a library of Ox's shape the first is the claim that matters, because of what structured concurrency is for.
A scope exists so that code can lend something it has to its forks and have it back when the scope completes: a
fork may use what the body's caller owns because no fork outlives the scope. The claim is the rule that makes that
lending sound:

> For every body, if the body, run with a scope's capability and what it is lent, keeps to what it is lent, then
> `supervised(body)` run with the same gives the body's result or the first failure, and when it completes
> everything lent is back, whichever way it completes.

In a logic of ownership it is three rules. Each is a triple: what a call needs, the call, and what it gives.

```
scope   {lent * P}  supervised(body)  {r. lent * Q r}    and    {lent * P}  supervised(body)  {fails e. lent}
        when, for every capability ox:  {scope(ox, lent) * P}  body(ox)  {r. Q r}

fork    {scope(ox, lent) * P}  fork(f)(using ox)  {h. fork(h, R)}     when  {P}  f  {r. R r}
        and inside f, what `lent` holds may be used while the scope is open

join    {fork(h, R)}  h.join()  {r. R r}     or it fails, as the scope then does
```

`par`'s rule follows from them, and is the one FrFlow's own programs would use: `{P1} a {Q1}` and `{P2} b {Q2}`
give `{P1 * P2} par(a, b) {Q1 * Q2}`. Today FrFlow justifies steps at once by proving each two commute
(`commute_<i>`, Lipton's reduction); under this rule, two sides that own separate things need no such proof.

Below that rule are the claims about the protocol, which the rule is proven from and which users also read
directly. Each is a safety property, said of one run of a scope:

| Claim | In Ox's code |
|---|---|
| Containment: a scope completes only when every fork started in it has finished its body. | the set, the flag, the closing loop |
| Outcome: a supervised scope gives its body's result exactly when the body and every user fork succeeded; otherwise the first failure reported, the others suppressed under it. | the supervisor's counter and future |
| Cancellation is asked: when a scope ends, each fork still in the set is interrupted, once. | the closing loop |
| Clean-up: the finalizers run once, last registered first, after containment holds; registering later fails. | `getAndSet(null)` on the list |
| A fork's result: `join` gives what the fork's body gave. | the fork's future |
| Locals: a fork reads the values of the scope it was started in. | `ForkLocalMap`, `currentScope` |

What is not among them, and is not a claim of the usual proofs either: that a scope ever completes. That needs
every fork to answer an interrupt, and a fair scheduler; it is liveness, and has a section of its own below.

### What the model shows

`Herd.v` models the set, the flag, each fork's life, the owner, and each caller of `startThread` between its check,
its `add` and its `start`, each a step, interleaved in any order. Two theorems, proven with no axioms:

- `contained`: when only the owner and the scope's forks call `startThread`, once the owner is past the closing
  loop no fork is running its body, no start is under way, and no step is possible.
- `leaks`: when another thread holds the capability, a scope can complete with a fork of its own still to run. The
  other thread passes the check of the flag; the owner closes and finds the set empty; the thread then adds its
  fork and starts it.

Three things follow, each of which a claim would have to say:

1. **Containment has a premise: the capability stays inside the scope.** Ox's check
   (`verifyCurrentThreadInScopeTree`) asks whether the calling thread is in the tree of the scope it is itself
   in, not whether it is in the tree of the scope it forks into; by this reading a capability handed to a thread of
   a sibling scope passes it. Ox's own answer for threads outside is `inScopeRunner`, which sends the code to a
   fork of the scope. The premise is exactly what Scala's capture checking can say of a capability, and what
   FrFlow already takes from the compiler for a store (`Table^`).
2. **Containment does not use `interrupt` or `join`.** The loop ends when it finds the set empty; `join` only keeps
   it from spinning and `interrupt` only makes forks end. So the safety claims rest on little of `Thread`.
3. **Containment is of the fork's body, not of the thread.** A fork takes itself out of the set as its last step
   and is, for a moment, a live thread that is not in it. "Every fork has finished" must not be stated as
   `!thread.isAlive`.

The model leaves out nested scopes (a thread of an inner scope forking into an outer one: its owner is in the
outer set until the inner scope completes, so the same invariant, one level up), a failing `start`, and reads the
emptiness test as one step (below).

## 2. The claims needed, and what is assumed of Java's threads

### The assumptions

Ox's code is correct only relative to what the JDK's classes do. Each row is something the proofs would take as
given, and so something a developer would decide as an assumption.

| Of | Assumed | Needed for | Where it is promised |
|---|---|---|---|
| The memory model | A program whose shared state is `final` fields, volatiles, atomics and the concurrent collections runs as an interleaving of its threads' steps. | everything: it is what makes "steps, interleaved" the semantics | JLS §17.4.5 (programs free of data races). One field read here is neither: `customThreadFactory`, set once at start |
| `Thread.start` | The body runs once, on a new thread, after `start` was called; a thread made by the factory does not run until then. | containment | JLS §17.4.5, `Thread`'s documentation |
| `try … finally` | The `finally` runs however the body ends; nothing ends a thread from outside (`Thread.stop`, the JVM's own errors). | containment (the fork's removal from the set) | JLS §14.20.2; the second half is an assumption about the program |
| `Thread.currentThread`, `ThreadLocal` | A thread's identity is its own; a value a thread sets, only it reads. | the owner check, the current scope | their documentation |
| The concurrent set: `add`, `remove`, `contains` | Each takes effect in one step during its call. | containment | `ConcurrentHashMap`'s documentation |
| The concurrent set: `isEmpty` | When it answers `true`, the set was empty at some moment during the call. | containment (the loop's exit) | **not promised**: see below |
| The concurrent set: `forEach` | It passes over every element that is in the set from its start to its end. | cancellation | "weakly consistent" traversal |
| `AtomicInteger`, `AtomicBoolean`, `AtomicReference` | Each call is one step; `updateAndGet`'s function may run more than once. | outcome, clean-up | their documentation |
| `CompletableFuture` | Exactly one `complete` or `completeExceptionally` wins and says so; `get` returns only once it is completed, with what it was completed with, or fails as interrupted. | outcome, a fork's result | its documentation |
| `Thread.join` | It returns normally only when the thread has ended or was never started. | nothing in safety; the loop's efficiency | JLS §17.4.5 |
| `Thread.interrupt` | The thread's flag is set; a thread blocked in, or entering, `get`, `join`, `acquire`, `sleep`, `take` then fails as interrupted. | that a scope completes (liveness) | `Thread`'s documentation |
| `Thread.interrupt` before `start` | The request is kept and seen once the thread runs. | that a scope completes | **the reference implementation only**: "interrupting a thread that is not alive need not have any effect" |
| The scheduler | Every thread that can step, eventually does. | that a scope completes | nowhere as such |

Two rows are findings of the reading, not known defects; neither was reproduced by a run:

- **`isEmpty`.** The closing loop is `while !threads.isEmpty`, on `ConcurrentHashMap.newKeySet()`. The class's
  documentation says the aggregate status methods, `isEmpty` among them, are "typically useful only when a map is
  not undergoing concurrent updates", and otherwise "adequate for monitoring or estimation purposes, but not for
  program control". Forks add forks and remove themselves during the loop. A proof needs the row above as an
  assumption the JDK does not make, or the code needs another test of emptiness (a counter of its own).
- **An interrupt before `start`.** The loop interrupts each thread once (`interruptedThreads`), and a thread is in
  the set before it is started. If that interrupt has no effect, as the specification allows, a fork that would
  run forever is never cancelled. It concerns liveness only.

### Can they be FrSpecs of `Thread`?

In part, and the part that cannot is the reason new assertions are needed.

- **What is data is an `FrSpec` today.** A thread's identity is an id (`opaque type ThreadId` with
  `FrSpec.Opaque`); a thread's status and a future's state are enums; the supervisor's and the set's states are
  case classes with contracts.
- **What is one step on a state is a model today.** `AtomicInteger`, `AtomicBoolean`, `AtomicReference`, the set's
  `add`, `remove` and `contains`, and `CompletableFuture.complete` are each an operation of a `StateModel`, with
  `stored.atomic` as the assumption. The model's Scala can be the JDK class itself, given with
  `defineOperations` and so tested against the model on generated runs, two calls at once among them. That turns
  "trusted" rows into tested ones.
- **A library known by what is assumed of it is a `provided` structure today**: `Declaration[Threads]`,
  `threads.provided`, and an assumption per row.
- **What cannot be said** is the content of the rows about `start`, `get`, `join` and `interrupt`. An `FrSpec`'s
  contract is a rule every value of a type meets, at one moment. These rows are about a second thread and about
  waiting: "the body runs, at once with the caller", "returns only once". FrFlow's statements speak of one run
  from the current world; "two runs in sequence, and 'eventually', cannot be stated", and a call among others
  (`call.amongOthers`) is one thread seen under interference, with no way to say what another thread has done.

So the proposal is the developer's idea with one change: a type's spec gets a second half, beside its contract.
The contract stays the rule on the type's values; the new half is the type's protocol: a state of the logic for
each object, and for each method what it needs and gives of that state. As with a contract, it enters the model
only when a node states it, decided as an assumption for a JDK class and as a claim for a class FrFlow reads.
A sketch, in names that do not exist:

```scala
object JThread extends FrSpec.Protocol[Thread]:
  enum Life derives FrSpec { case Made, Started, Ended }
  val life = ghost[Life]("where a thread is: made, started, ended")            // only statements read it
  rule("a thread ended stays ended")(life.stays(_ === Life.Ended))
  method(_.start())(needs = owns(life, Life.Made), gives = forked(body) sep knows(life =!= Life.Made))
  method(_.join())(gives = knows(life === Life.Ended || life === Life.Made))   // partial: when it returns

val startRunsOnce = Node.assumption("A thread started runs its body once, at once with its starter.")(
  protocolOf[Thread](_.start()))
```

The JDK's rows then sit in one place, are decided once, and each of Ox's claims lists those it rests on
(`.assuming`): containment lists five of the table's rows, none of them `join` or `interrupt`.

### The claims, as a graph

Roots: the scope rule (as lending, "exactly" what was lent comes back), and the outcome ("exactly when the body
and every user fork succeeded"). Parts under the scope rule: containment, the fork and join rules, clean-up. Parts
under containment, which are the invariant of `Herd.v`: a fork running its body is in the set; a caller between
check and start is the owner in its body or a running fork; a thread added and not started is in the set, by one
caller; the loop leaves only on an empty set. Under the outcome: the counter is the user forks started and not
yet succeeded; the body is a user fork; the future is completed once, by the first to report. Assumptions: the
table's rows, and confinement, which is either an assumption about Ox's callers or, with capture checking, what
the compiler says. Design nodes: what no proof covers (the uncaught-exception handler, the thread factory).

## 3. The operators a claim needs

Each row is an operator claims do not have, with what it is in Iris and what FrFlow has that is nearest.

| Operator (names proposed) | Says | In Iris | Nearest in FrFlow today |
|---|---|---|---|
| `p sep q` | `p` and `q` hold of separate parts of the state | `P ∗ Q` | none in claims; in code, separation checking (`Table^`) |
| `owns(x, v)`, `reads(x, v)` | this thread alone may change `x`; several may read it | `x ↦ v`, `x ↦{q} v` | a structure's state, held exclusively; Scala's `rd` |
| `call.needs(p).gives(r => q)`, `.givesOnFailure(e => q)` | from a state meeting `p`, among any other threads, the call does not go wrong, and if it ends it meets `q` | `{P} e {Q}`, a weakest precondition with a postcondition per outcome | `call.result`, `.after`, `.ifSucceeds`, `.ifFails`: one run, alone |
| `call.atOnce(before => after)` | the call takes effect in one step, somewhere during it | a logically atomic triple `⟨P⟩ e ⟨Q⟩` | `stored.atomic`; `defineOperations` tests it |
| `forked(body)` | a thread running `body`, at once with this one | the thread pool; the `fork` rule | `parTupled`, `race` (the sides read in turn); no thread started and left |
| `kept(inv)`, `kept(inv).during(scope)` | `inv` holds at every step of every thread; or while a scope is open, and is handed back after | an invariant `inv N I`; a cancellable invariant or a borrow | `always(stored)(inv)`: between runs, for every program that writes the model |
| `p.stays` | once `p` holds it holds from then on | a persistent fact `□ P` over monotone ghost state | `t.isConstant` (never changes) |
| `ghost[A]`, `records(…)` | a word only statements read, changed at a step of the code | ghost state `own γ a` and its updates | a word no code reads; `tracks` (a state by its history) in the Lean library |
| `awaits(cond)` in a model | a step that can be taken only when `cond` holds | a blocking call: a loop, or a triple taken as given | none: every operation of a model can always step |
| `forall(body meeting claim)` | every piece of code that meets a claim | a triple inside a triple | a class given the words of the structures it holds, proven from the claims on them |
| each pass of a loop keeps `inv` | a loop's invariant | Löb induction, the later modality `▷` (kept out of sight) | none: a loop is not read |

Four of these are new kinds of assertion: ownership (`sep`, `owns`), a call among threads (`needs`/`gives`,
`atOnce`), facts that stay with their ghost words (`stays`, `ghost`), and waiting (`awaits`). The others extend
what exists: `kept` is `always` said of every step, `forked` a combinator, the quantifier over code a `provided`
word. Failure needs nothing new. FrFlow already reads a failing call as a value (`.result` is an `Either`), and
Java's interruption is cooperative: a flag on the thread, and blocking calls that fail when it is set. It is a
field of the thread's state and one more outcome of each blocking call.

What the operators stand on is a different reading of code. Today a member is read as a function of the state
that gives the state after it, and a call among others as that function with the state replaced between steps.
Threads need the code as steps: a small language in Rocq with a heap, compare-and-set, `fork`, a thread's id and
its locals, and a step relation over a pool of threads, which is what Iris is instantiated with. The TASTy reader
(`dsl.compiled`) would give a member's body as an expression of that language instead of a term, and loops (the
closing loop, `takeUntilSuccess`) would have to be read, which they are not today.

## Liveness: that a closing scope completes

It can be proven in plain Rocq once Ox is compiled to steps, and plain Rocq is the better place for it.

- **Why not in Iris.** Iris's triples are defined by counting steps: a triple holds of a program up to any number
  of steps, so a program that runs for ever meets every triple. They say what a call gives if it ends, never that
  it ends. Proving that it ends takes an extension that relates the program to a model with fairness (Trillium
  and its kin).
- **Why in plain Rocq.** Over a step relation a run is a sequence of states (`nat -> state`), "eventually" is
  `exists n`, and fairness is a property of the sequence. No logic is needed, only induction.
- **What "compiled" must mean.** A step relation that names the thread taking each step. Today's reading gives a
  member as a function from the state to the state after it, which has ended by being a function; the closing
  loop has no such reading. It is the same compilation the first route below needs.

`Closing.v` is the proof on a model of the closing phase: the forks in the set when the scope starts to close,
the owner interrupting each once and leaving when none is left, a fork spinning or ending until it is interrupted
and taking a bounded number of steps after. Its theorems:

- `closes`: in every fair run the owner gets past the loop.
- `needs_fairness`: with one fork, the run in which the fork spins for ever is a run in which the owner never
  leaves; it is unfair to the owner alone.

The proof has three parts, which are what a claim of this kind would ask for: a rank (one for the owner's
leaving; for each fork in the set its bound, one for its ending, one more while it is not interrupted); that no
step raises the rank and every step lowers it but a fork's spinning before its interrupt; and that until the
owner has left something can step. Fairness is used once: while a fork spins, the owner's interrupt can be made
at every moment, so it is made. Once every fork is interrupted every step lowers the rank, so from there the
bound holds with no fairness at all: that is the bounded form of the claim.

What it assumes beyond safety's rows, each a decision of the developer's:

| Of | Assumed | Note |
|---|---|---|
| a fork's body | Once interrupted it ends within a bound, and starts no fork. | A body that catches the interrupt and blocks again is never interrupted a second time: the loop interrupts once. Said of the body's steps, since a body is a parameter. |
| `Thread.interrupt` | The request reaches the fork, also when made before the fork's first step. | The second half is the reference implementation's behaviour only (section 2). |
| blocking calls | A thread blocked in `get`, `join`, `acquire`, `sleep` or `take` when interrupted fails as interrupted. | their documentation |
| `Thread.start` | It does not fail. | A thread added to the set and never started stays in it. |
| the scheduler | An actor that could step at every moment from some moment on, does step. | Not true of virtual threads as such: they are not time-sliced, so forks that compute without blocking, as many as there are carrier threads, keep the owner from running. It holds when bodies block or yield, which makes it an assumption about bodies too. |

What the model leaves out: the starts under way when the scope closes (at most one per running fork, so a finite
addition to the rank), nested scopes (an inner scope's closing is how its owner, a fork of the outer, answers the
interrupt: an induction on depth), the owner's waiting in `join` (here its steps are the interrupts and the
leaving), the finalizers, and the body's phase, in which nothing need end.

What FrFlow would need:

- **A claim that something comes about**: `closing.leadsTo(completed).by(rank)`, the rank given by the developer
  as a term over the state. Its checks are the proof's parts: every step keeps or lowers the rank, the steps that
  keep it are named, something can step until `completed`, and the named steps cannot go on for ever under the
  fairness assumed.
- **Fairness as an assumption about the world**, of the kind a clock's `schedule` is (a trusted fact restricting
  the world's steps): `fair(owner)`, `fair(fork)`.
- **The proof on the compiled steps, not on a model beside them.** A model related to the code by a simulation
  carries safety down to the code, and carries liveness only when the code's steps that the model does not see
  cannot go on for ever, which is a rank again. Stating the rank on the compiled steps is one proof instead of two.

What plain Rocq does not give is what it does not give for safety: a rule about any body with what it owns. Here
a body enters as the first row of the table, a fact about its steps.

## No lost wake-up

A wake-up is lost when a thread waits, what it waits for has come about, and nobody will tell it. That it does
not happen can be proven, and most of it is safety, so it is easier than the section above. The claim has two
halves:

- **An invariant**: whenever what a thread waits for has come about, the signal has been given or a thread is on
  its way to give it. No fairness, no rank.
- **That the waiter then runs**: the thread on its way gives the signal, and the waiter takes it. This half is
  liveness, with the same fairness as above, and short: the invariant has already named who must step.

### Where Ox waits

Ox's core has no `wait`/`notify` and no `Condition` (searched in the sources read; channels and `Flow` apart).
Every wait is on a JDK class that latches: a signal given before the wait begins is still there when it does.

| The wait | What is waited for | Who signals | Latch |
|---|---|---|---|
| the owner of a supervised scope, `result.get()` | every user fork succeeded, or a fork failed | the fork whose decrement of the count reads zero; the first fork to fail | `CompletableFuture` stays completed |
| `Fork.join`, `result.get()` | the fork's result | the fork, when it succeeds | the same |
| the closing loop, `thread.join()` | the thread has ended | the thread's end | a thread ended stays ended |
| a cancellable fork's outer thread, `done.acquire()` | the inner fork is done, or was cancelled | the inner fork; `cancelNow` | a `Semaphore`'s permits are counted |
| `race`, `result.take()` | a branch has a result | each branch, `result.put` | the queue keeps its elements, and has room for every branch |
| `never`, `LockSupport.park()` in a loop | an interrupt | `Thread.interrupt` | the flag is checked after each return |

So the check-then-wait race (the signal falls between a thread's check and its going to sleep) can only be
inside those classes. That they latch is an assumption, a line of each class's protocol in section 2. What is
left for Ox's own proof is the other way to lose a wake-up: a path that brings about what is waited for and
does not signal.

### The supervisor, in the model

[threads/Wakeup.v](threads/Wakeup.v) is that proof for the first row. A user fork's success is two steps,
`running.decrementAndGet()` and then `result.complete(Success)` when it read zero, with any other thread's steps
between them; a daemon fork may start a user fork at any time, also when the count is zero. Three theorems, with
no axioms:

- `no_lost_wakeup`: when the future latches, once a user fork has been started and none is in its body, the
  future is completed, or a fork is between its decrement to zero and its completing the future.
- `done_stays`: a completed future stays completed.
- `lost_without_latching`: when a signal reaches only an owner already parked, the wake-up is lost: the one fork
  decrements and signals while the owner is still arriving, and the owner then parks, with no fork left.

The invariant is three facts: the count is the forks on it; a failure has completed the future; and while the
future is not completed and the count is zero, either no fork was started or one is between its two steps.

### What the reading found

Of the second row. In a supervised scope a fork that fails or is cancelled never completes its own future: the
supervisor takes the exception (`forkException` returns `true`), and the code's comment says "any joins will end
up being interrupted". That holds for a joiner the scope interrupts, a fork of the scope. A joiner the scope does
not interrupt waits for ever:

```scala
val f = supervised { fork { sleep(1.hour) } }   // the scope ends, the fork is cancelled, its handle leaves
f.join()                                        // nothing completes the future, nothing interrupts the caller
```

It is not a signal lost in a race; it is a wait that has no signaller, and it shows as the premise the proof of
the second row would need: a fork is joined only by threads of its scope, while the scope is open. It is
containment's premise again, of the fork's handle this time. Read from the sources, not run.

### What FrFlow would need

Nothing beyond section 3's operators. The invariant is `kept` over every step, with a ghost word for "what is
waited for has come about", and `awaits` in the model of each JDK class says when its wait can return. The
check FrFlow would derive for each wait is the invariant above: at every step that brings the condition about,
the signal is given in that step, or the thread is named that gives it next.

## Two routes, and the order

**The protocol, first-order.** State Ox's scope as a model whose state has a field per thread, give each method's
steps, and prove the invariant: `Herd.v`, grown to the supervisor and the finalizers, then generated from the
code. It needs three things of FrFlow: a model's state indexed by a thread's id with threads added as it runs,
`always` said of every step, and `awaits`. It needs no Iris, runs on Rocq's standard library as the generated
files do now, and proves the protocol claims of section 1 and, with a rank and fairness, that a closing scope
completes. It does not give the scope rule: it says nothing of what a body owns.

**The rules, in Iris.** Add the language and the four kinds of assertion, take the JDK's rows as protocols, prove
Ox's methods against them, and derive the scope, fork, join and `par` rules. Iris's adequacy theorem speaks of the
main thread's result and of invariants, not of the other threads having ended, so containment is still stated as
the first route's invariant, tied to ghost state; the first route's work is kept. Automation for such proofs
exists (Iris's proof mode; Diaframe), which matters for `frflow_auto`.

The recommended order is the first route, then the second, with the JDK's protocols written once and used by
both: the first is close to what FrFlow is, finds the same assumptions (this page's findings came from it), and
its invariants are what the second needs.

## What is left out

- **Liveness beyond the closing loop**: that `join` returns, that a supervised scope ends once its user forks
  have, that `race` gives a result. Each is a rank of its own over the same steps and the same fairness.
- **Channels, `Flow`, the resilience package**: channels are jox's, an algorithm of the kind proven by
  linearizability; a different proof from the scope's.
- **Weak memory**: taken away by the first row of the table, which is itself a claim about Ox's fields that a
  reader of the code can check.
- **Ox's own effects outside the model**: the uncaught-exception handler, `OxApp`, the thread factory.

## Where it stands

- [examples/ox/rocq/Ox](../examples/ox/rocq/Ox/README.md): containment proven of Ox's code against the JDK's
  contracts; `sh examples/ox/rocq/check.sh` (Rocq 9.3, under a minute). About 3,900 lines with the library in
  `modules/proof/rocq/FrFlow/Threads`. Not part of `sbt rocqTest` yet.
- [threads/Herd.v](threads/Herd.v): the first model and its two theorems; `rocq compile docs/threads/Herd.v`
  (about a second). It is not part of `sbt rocqTest`.
- [threads/Closing.v](threads/Closing.v): the closing phase and that it ends under fairness;
  `rocq compile docs/threads/Closing.v`. It uses excluded middle (`classic`), as FrFlow's Rocq library does, and
  is a model of its own: it is not derived from `Herd.v`'s, whose forks have no interrupt and no bound.
- [threads/Wakeup.v](threads/Wakeup.v): the supervisor's count and future, and that the owner's wake-up is not
  lost; `rocq compile docs/threads/Wakeup.v`. No axioms. A third model of its own.
- Iris is not installed where this was written: the machine has Rocq 9.3 with its standard library, opam's default
  repository has no Iris package, and the network policy denied the hosts that have it (`gitlab.mpi-sws.org` for
  the sources of Iris and std++, `rocq-prover.org` and `coq.inria.fr` for the package archive). No rule on this
  page was checked in Iris.
- The reading of `isEmpty` and of an interrupt before `start` is of the sources and the JDK's documentation;
  the capability check and the `join` outside the fork's scope were also run (`examples/ox/probe`). None is
  reported to Ox.
