# Ox, proven in Rocq against the JDK's contracts

That no fork outlives its scope ("containment"), proven of Ox 1.1.0's scope and fork code, for every client that
keeps one stated condition and any nesting of scopes, from contracts on the JDK's classes. Rocq 9.3, its standard
library, no axioms.

```bash
sh examples/ox/rocq/check.sh
```

## What is proven

`Main.contained`. Take any client whose closures meet `client_ok` (below). Start the first thread on a closure of
the client's that holds no capability. In every configuration the threads reach, by any order of their steps:
once the first thread has ended, every other thread's remaining program is a return. No thread has an operation
of Ox's, of the JDK's or of the client's left to perform.

`Example.example_contained`. The same with nothing assumed of the client, for one client: a supervised scope
whose user fork forks again and opens an inner unsupervised scope, whose own fork holds the outer scope's
capability.

`Laws.scope_contained`, of any scope at any depth, while the rest of the program runs on. Once a scope has
completed (its closing loop has found its set of threads empty), in every configuration reached after: it is
completed, its set is empty (no thread is ever added to it again), and no fork of it has an operation left.
`Laws.scopes_nest`: a scope opened inside a completed scope is completed, so an inner scope completes before the
one enclosing it. These are laws 1, 2 and 3 of `docs/THREADS.md`'s list of what a library of scopes owes its
users; `Laws.v` says how each of the seventeen stands.

Along the way, of each method (the "claims on members" the theorem is built from):

| Method | Needs | Gives |
|---|---|---|
| `new ThreadHerd` | the caller has not ended | a herd is opened, owned by the caller, innermost of its open herds |
| `startThread` | the caller is inside the herd; the body holds only capabilities of herds enclosing it | the ghost state as the caller left it; the new thread has what it needs |
| a fork's thread | what `startThread` handed it | it ends owning no open herd, out of its herd's set |
| `interruptAllAndJoinUntilCompleted` | the caller owns the herd, innermost | the herd is exited and popped, in every outcome; nothing is thrown before the set is found empty |
| `forkError`, `forkUserError`, `forkUnsupervised`, `fork`, `forkUser` | as `startThread` | as `startThread` |
| `scopedWithCapability` | the capability's herd is the caller's innermost open herd | the herd is exited and popped, whatever the body and the closing do |
| `unsupervised`, `supervisedError`, `supervised` | the caller is inside the herd of every capability the closure holds | the ghost state as the caller left it |
| `DefaultSupervisor`, `NoOpSupervisor`, `Fork.join`, the casts | nothing | they touch nothing the invariant reads (found by a tactic) |

## What is asked of a client

`client_ok`: each closure of the client, called by a thread that is inside the herd of every capability the
closure holds or is given, leaves the ghost state as its caller left it. A client meets it by calling Ox through
the rules above. The rule for a fork carries the condition that matters:

> A closure forked in a scope holds only that scope's capability and those of scopes enclosing it.

Lexical scoping does not give this: `fork(using outer) { fork(using inner) { … } }` type-checks, and Ox's
run-time check passes it (it asks whether the caller is in the tree of its own scope, not of the scope it forks
in). The proof shows where it is needed: `threads.add(thread)` on a herd whose closing loop has already found
the set empty.

## Run against Ox itself

`examples/ox/probe` runs Ox 1.1.0 (`cd examples/ox/probe && sbt "run 200000"`; Java 21). Three behaviours the
proof and the reading predict, all seen:

- **The condition on the client is needed.** A fork of an outer scope is handed an inner scope's capability and
  forks into it as the inner scope ends. In two runs of 200,000 rounds, 7 and 21 forks of the inner scope ran
  uninterrupted after the inner scope had completed (9 and 40 forks got past the shut-down check; the rest
  were refused with `IllegalStateException`). Ox's run-time check passed every one.
- **A `join` outside the fork's scope.** `val f = supervised { fork { sleep(1.hour) } }; f.join()` was still
  blocked after 5 seconds: a fork cancelled by its scope's end never completes its own future.
- **A user fork that is refused is still counted.** `forkUser` adds one to the supervisor's count before
  `startThread` can refuse the fork. A thread outside every scope, handed the capability, called `forkUser`;
  it was refused with `IllegalStateException`, and `supervised` was still blocked 5 seconds after its body had
  returned: the count never comes back to zero.

None is reported to Ox. Each uses a capability or a fork outside the scope it belongs to; whether Ox should
catch that is Ox's to say. The proof shows that containment does not hold without the condition on the client.

A fourth run is of the JDK alone, and bears on the first assumption below (`IsEmptyProbe`,
`sbt "runMain IsEmptyProbe 30 2"`): a `ConcurrentHashMap.newKeySet()` that always holds one element, other elements
added by one thread and removed by another (as a fork is added by the thread that starts it and removes itself),
and a thread asking `isEmpty`. On JDK 21.0.12, in 30 seconds, `isEmpty` answered `true` 44 times of 717 million:
of a set that was never empty. The closing loop of a scope ends when `threads.isEmpty` answers `true`. So the
contract `TsIsEmpty` that `contained` rests on is not one the JDK keeps, and a scope of Ox can in principle
complete with forks of its own in its set, whatever the client does. `EmptyProbe` looks for that in Ox itself
(forks that start short-lived forks as their scope closes): none in 20,000 rounds of 4 such forks, nor in
150,000 rounds of 16 (2.4 million forks); the window is a few nanoseconds of the owner's thread. In the longer
run 498 of the 2.4 million forks slept their 30 milliseconds without being interrupted while their scope was
still closing; on a loaded machine the probe cannot tell an interrupt that came late from one that did not
come. The JDK's own `ThreadFlock` does not ask `isEmpty`: it keeps a count of its
own.

## What is assumed

1. **`Jdk.v`, every line.** Each JDK class Ox uses is its state and a contract per method; a call is one step
   among other threads' steps (linearizability, and the memory model's guarantee for code without data races).
   Two contracts say more than the JDK's documentation:
   - `TsIsEmpty`: `ConcurrentHashMap`'s `isEmpty` answers `true` only of a set empty at that moment. Its
     documentation says the method is "not for program control" under concurrent updates. It is not kept: a run of the
     JDK shows `true` of a set that was never empty ("Run against Ox itself"). `contained` is therefore a
     theorem about Ox with an emptiness test that is exact, which Ox 1.1.0 on the JDK does not have.
   - `TypeError`: a cast the compiler inserted does not fail (the JVM's type safety). A cast the source
     writes throws `ClassCastException` when it fails.
2. **`Gen.v` is Ox.** It is generated from the TASTy in Ox's published jar by rules over Scala's constructs
   (`docs/THREADS-GENERATOR.md`), and it is what every proof here imports. What is trusted of it: the rules,
   the tables that say which JDK method is which operation, and the Scala compiler's TASTy reader. `Code.v` is
   the same unit translated by hand before the generator existed; the two are the same text, comments and
   spacing apart, and `Agree.v` proves each definition equal by `reflexivity`. The generator found two
   differences in the hand translation, since corrected (a parameter order; a cast the source writes, which
   can fail).
3. **Code that is not read.** `ErrorMode` and `ForkLocalMap`: their methods are taken to touch nothing of the
   state here (`Extern`: any result, no effect). `uninterruptible` inside `runFinalizers`: `Chaos` (anything may
   happen); the proof shows it is not reached when no finalizer is registered, and the client model has no way to
   register one.
4. **Not modelled**: integer overflow, a thread ended from outside (`Thread.stop`), errors of the JVM itself, a
   `Throwable`'s identity and its suppressed exceptions (`addSuppressed` does nothing).

## What is not proven

- That anything ends. `contained` says what holds once the first thread has ended, not that it does.
- The outcome of a scope (the body's result or the first failure), that forks are interrupted, that no wake-up is
  lost: on Ox's code. (`docs/threads/` has the last two on hand-written models.)
- `forkCancellable`, `par`, `race`, `timeout`, resources and finalizers, channels, `Flow`.

## The files

Library, `modules/proof/rocq/FrFlow/Threads/` (logical path `FrFlow.Threads`):

| File | What it is |
|---|---|
| `Prog.v` | A program: returns, calls one operation of a library, loops, calls a closure. |
| `Jdk.v` | The assumptions: each JDK class Ox uses, its state and a contract per method. |
| `Sem.v` | Threads: a configuration, and one thread's step at a time, in any order. |
| `Logic.v` | `wp`: an invariant, ghost state, a rely; a rule per kind of step. `sound`. |
| `Lang.v` | What Scala's constructs are read as. |

Ox, `examples/ox/rocq/Ox/` (logical path `Ox`):

| File | What it is |
|---|---|
| `Gen.v` | Ox's scopes and forks as programs, generated from Ox's TASTy. What the proofs are about. |
| `Code.v`, `Agree.v` | The same unit by hand, and that the two agree. |
| `Ghost.v` | The ghost state, the invariant `Inv`, the rely `Rely`. |
| `Facts.v` | Being inside a herd; a herd with a thread inside it is not exited. |
| `Specs.v` | What is asked of and given by each closure; the rules for throwing programs. |
| `Frame.v` | Operations and programs that touch nothing the invariant reads. |
| `Updates.v` | Each step that changes what the invariant reads keeps it. |
| `Steps.v`, `Inner.v` | Rules for one operation; the innermost herd; the order of herds. |
| `HerdProofs.v` | `ThreadHerd`, method by method. |
| `ScopeProofs.v` | The forks and the closures Ox makes. |
| `Main.v` | Every closure meets what is said of it; `contained`. |
| `ApiProofs.v` | `scopedWithCapability`, `unsupervised`, `supervised`, `fork`, `forkUser`, `join`. |
| `Example.v` | A client, and containment for it. |
| `Laws.v` | The laws of a scope that are theorems here: containment of one scope, that it stays closed, nesting. |
| `Tree/` | All of Ox, not only its scopes and forks: the tree of each of its 116 TASTy files (below). |

## All of Ox, and what it rests on

`Tree/` holds Ox 1.1.0 whole, read a second way: each TASTy file of its jar as the tree the compiler typed
(`modules/proof/rocq/FrFlow/Scala/Tree.v`: a constructor for each form of tree and of type), with nothing chosen
in the reading. 116 files, 38,939 trees; the reading is checked against the compiler's own traversal, which counts
the same number of each form (`OxSourceSuite`). The proofs above are not about these trees yet: they are about
`Gen.v`, read by rules from the scopes and forks. What Rocq computes from the trees, and checks kept lists
against:

| File | What Rocq checks |
|---|---|
| `Tree/All.v`, `Tree/Surface.v` | Ox's trees are closed (nothing of Ox is referred to and not defined), and take 513 definitions from outside: the JDK, Scala's library, jox. |
| `Tree/Kernel.v` | The operators of Ox's concurrency (scopes, forks, fork locals, resources, `par`, `race`, `timeout`, control) reach 320 of the 2,460 definitions Ox makes, and take 184 from outside, 68 of them the JDK's. |
| `Tree/Assumed.v` | Each of those 68 has its standing: 43 under a contract of `Jdk.v`, 21 data, 4 trusted. None is left out. |
| `Tree/Memory.v` | The memory-model assumption (no data race, so threads' steps in turn), and its half about Ox: the kernel's classes declare nine variables; five are reached by one thread, three are captured only by functions a set's `forEach` runs on its caller, one is a field trusted to be set before any scope opens. |

## The design of the proof

- **Ghost state.** Per herd (named by the reference of its `threads` set): owner, `h_exited` (its closing loop
  has found the set empty), `h_parent` (the herd it was opened inside), `h_stamp`. Per thread: `g_role` (`Main`;
  `Created t th b`: made by `t`, not yet in a set; `ForkOf h b`: in herd `h`'s set, or once in it), `g_removed`
  (it has run its `threads.remove`), `g_open` (the herds it owns that are not exited, innermost first).
- **Where it changes.** `newKeySet` in `ThreadHerd`'s constructor: the herd is registered and pushed.
  `newThread`: `Created`. `threads.add`: `ForkOf`. `threads.remove` by the fork: `g_removed`. `isEmpty`
  answering `true` in the closing loop: `h_exited`, popped.
- **Inside.** `inside Γ u h`: `u` is an unremoved fork of some `h0`, or owns `h0` open, and `h` is `h0` or an
  ancestor of it. `Facts.inside_open`: a herd with a thread inside it is not exited. It is what `threads.add`
  needs, and it is the thread's own to know: its role, its flags, its open herds, and parent links that never
  change.
- **A call leaves the ghost state as its caller left it** (`Keep`): what every step keeps (`Ext`), and the
  caller's own flags and open herds. Only opening and closing a herd say more.
- **The end.** A thread that has taken itself out may not step (`Active`), so its program is a return. When the
  first thread has ended it owns no open herd; then no herd is open, by descent on `h_stamp` along owners
  (`Inner.no_open_herd`); then every fork has taken itself out.

## In FrFlow's terms

| Here | In a FrFlow model |
|---|---|
| a JDK class in `Jdk.v`: its state and its methods' contracts | a `provided` structure with an assumption per member |
| a method's rule in `HerdProofs.v`, `ScopeProofs.v`, `ApiProofs.v` | a claim on a member of a structure read from its class |
| `client_ok` | an assumption on what comes from outside |
| `contained` | the root |
| `Inv` | an `always` over every step of every thread |
