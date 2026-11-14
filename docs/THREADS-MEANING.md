# The meaning of Scala's trees, in Rocq

`docs/THREADS-GENERATOR.md` describes two readings of Scala into Rocq: by rules into programs (`Gen.v`), and whole
into trees (`examples/ox/rocq/Ox/Tree`). This page is about what the second now has: a meaning. Each tree the
compiler typed is given the program it runs, in the language the proofs about threads are in
(`FrFlow/Threads/Prog.v`), over the same operations of the JDK and the same contracts (`FrFlow/Threads/Jdk.v`).
The step relation of `FrFlow/Threads/Sem.v`, with this meaning for a call, is a step semantics of the trees.

It is tested: programs written against Ox are read into trees as Ox is, their meaning is run in Rocq over Ox's
own trees, and each must give what the same method gives on the JVM.

## Where it is

| What | Where |
|---|---|
| Values, objects, closures, how a program ends | `modules/proof/rocq/FrFlow/Scala/Value.v` |
| A program's classes and members, found by name | `FrFlow/Scala/Table.v` |
| The meaning of a tree: `denote`, `interp` | `FrFlow/Scala/Meaning.v` |
| What is taken from outside the program: the JDK, Scala's library | `FrFlow/Scala/Library.v` |
| Running it: one behaviour for each contract, threads in turn | `FrFlow/Scala/Run.v` |
| Where it stops, found without running | `FrFlow/Scala/Gaps.v`, `examples/ox/rocq/Ox/Tree/Meant.v` |
| The programs run, their trees, what Rocq checks of them | `modules/project/src/test/…/rocq/clients`, `examples/ox/rocq/Ox/Client` |
| The suite | `frflow.project.rocq.OxRunSuite` |

```bash
sbt "project/testOnly frflow.project.rocq.OxRunSuite"          # runs the programs on the JVM, compares the kept files
sbt "project/Rocq/testOnly frflow.project.rocq.OxRunSuite"     # Rocq runs their meaning over Ox's trees
FRFLOW_ROCQ_WRITE=1 sbt "project/testOnly frflow.project.rocq.OxRunSuite"   # writes the kept files anew
```

## What a tree means

`denote e t` is the program of the tree `t` where the variables in scope are `e`. It is defined by recursion on
the tree, a case for each form; nothing is looked up by a method's name, and Ox is not mentioned.

- **Values** are not typed: a number, a truth value, a text, a thread, a list, data of a class of Scala's library
  (an option, a tuple, an `Either`), a closure, or a place in the heap with its class.
- **A closure** is its tree and the scope it was made in. A by-name argument is one. Calling it is a `Call` of
  `Prog.v`, which `interp` answers with `denote` of the body: so a call is a step, and recursion is not
  recursion of Rocq's.
- **An object** of a class of the program is a place in the heap (`ObjNew`); a field read or written is one step
  of the thread (`ObjGet`, `ObjSet`), another thread's step may come between two of them. A `var` is an object
  with one field. An object of a class written inside a method keeps the scope it was made in.
- **A method call** on an object runs the nearest definition among what the object's class inherits from that is
  the method or overrides it: the compiler records what each definition overrides, and the tree keeps it.
- **An exception** thrown ends each program it passes through until a `try` takes it; `finally` runs either
  way; `return` ends the method it names.
- **A `lazy val`** is evaluated by the first thread that reads it; a thread that reads it meanwhile waits. Of a
  member, an interrupt ends the wait with `InterruptedException`; of one written in a method, it does not. If
  the evaluation throws, the next read evaluates again. This is the contract `LazyEnter` of `Jdk.v`, and it is
  what Scala 3.10 does on JDK 21 (`examples/ox/probe/LazyProbe.scala`).
- **A type test** (`case e: Throwable`, `isInstanceOf`) asks whether the value's class inherits from the class
  named. A type alias is read with the type it names (`TyAlias`), so `scala.Throwable` is
  `java.lang.Throwable` because the compiler says so, not because a table does.
- **What is outside the program** has the meaning `Library.v` gives it. A method of the JDK is the operation of
  its contract and nothing more is assumed of it; `AtomicReference.updateAndGet` is the loop the JDK documents
  (read, apply, compare and set, again if another thread came between). Scala's data is data and a method of
  it the function it is.

Where no meaning is given, the program is `stuck`: the operation `Chaos`, of which a proof may assume nothing and
at which a run stops and says why.

## What differs from the JVM

- **When an object's initialiser runs.** The JVM initialises an object (a Scala `object`) when it is first used.
  Here the objects with state that a program may reach are initialised by the first thread before the program
  starts. The two differ only if an initialiser does more than make objects; those of Ox's kernel (an enum's
  values, a thread local, a variable for the thread factory) do not.
- **Texts.** A text built from values (`s"…"`, `toString`) is not known: it is `Text`, equal to nothing.
- **Exceptions of the JDK** carry no message, no stack and no suppressed exceptions; one made by the program's
  own class is an object and has its fields.
- **Numbers.** `Int` and `Long` wrap as the JVM's do; there are no floating-point numbers.
- **Time.** `sleep` is a step that an interrupt ends; it does not wait. `nanoTime` gives a number that does not
  decrease.

## How it is tested

`clients` holds 25 programs against Ox 1.1.0, each a method that answers a number.

- 18 use the operators (`Joins`, `Failures`, `Scopes`): a scope with nothing forked, forks joined, a fork that
  throws (joined, or only waited for), a body that throws while a fork sleeps, a fork interrupted when its
  scope ends, a fork not supervised, a fork cancelled, an application error, a scope inside a fork, `par`,
  `raceSuccess`, `timeout`, finalizers and their order, a resource released at the scope's end, a fork local
  set for a scope.
- 7 observe a law (`Observed`): each fork sets a flag as its last act, and the program answers which flags
  were set once the scope had ended. A scope returns after the forks it waits for have finished; a scope that
  ends interrupts the forks still running and returns after they have ended; a failing fork has its sibling
  interrupted and ended before the scope throws; an inner scope has ended, forks and all, before the code
  after it runs; a finalizer runs after the forks have ended; a scope not supervised does the same; `cancel`
  returns after the fork has ended. These are the laws of containment and cancellation as a program can see
  them: checked on these runs, not proven.

Writing the last one showed a behaviour of Ox worth knowing: a fork made by `forkCancellable` and cancelled
before its thread has started never runs its body (`cancel` then gives the interrupt). Whether a fork cancelled
at once runs is the scheduler's choice; the program here waits until the fork runs before it cancels.

`OxRunSuite` runs each on the JVM, reads the programs' TASTy into trees, and writes `Runs.v`: over the programs'
trees and Ox's 116, one lemma for each program, that under each of four orders of the threads' turns (each
thread in turn, and three shuffled orders) every thread ends and the first gives the number the JVM gave. Rocq
proves each by running the meaning (`vm_compute`): a hundred runs.

What this shows is that the meaning of the forms these programs and Ox's kernel use, and of the JDK's members
they call, agrees with the JVM on these runs. It shows nothing of the runs not made: the contracts allow the JDK
other behaviours than the one `Run.v` picks (a `compareAndSet` that fails, another element first in a
traversal), and there are more orders than four.

## Where it stops

`Gaps.v` finds what shows in the trees themselves, and `Meant.v` states it of Ox, checked by Rocq:

| | The kernel (320 definitions) | All of Ox (2,460) |
|---|---|---|
| Definitions with a tree of a form that has no meaning | 0 | 6 |
| Arguments given by name out of their place | 0 | 0 |
| Classes and objects declared inside a class | 0 | 9 |
| Definitions taken from outside with no meaning | 13 of 184 | 186 of 513 |

The kernel's 13 are a hash code and a serialization proxy the compiler makes for case classes and objects and no
operator calls, `Await.result` (an extension on Scala's futures), and nine of the compiler's own that only a
macro's code uses, when the compiler runs it. Beyond the kernel the meaning is not whole: channels (jox),
flows, reactive streams, input and output and much of Scala's collections have none yet, and a program that
reaches one stops there.

## What the proofs are about

The theorems of `examples/ox/rocq/Ox` (containment of a scope, that it stays closed, nesting) are about `Gen.v`:
the programs the rules read from Ox's scopes and forks. They are not yet about the meaning of the trees. The
two are the same language over the same contracts, and differ in how an object is held: `Gen.v` reads a class
into a record and a field into a projection, where the meaning here keeps the JVM's heap and makes each field
read a step. Until the proofs are moved, what joins the two is that both are read from the same TASTy, and that
the meaning here is the one tested against the JVM.

What moving them takes, as far as it was tried:

- **The logic applies as it is.** `Logic.v` is over any type of closures and objects and any `interp`; with
  `Value.code`, `Value.obj` and `Meaning.interp` its `sound` is about the trees.
- **A proof can walk the meaning.** Rocq reduces `interp` of a method of Ox to its first operation and what
  follows it (`lazy head`) in under half a second with all of Ox's trees in the table, so a method is proven
  as in `HerdProofs.v`, an operation at a time. The whole program of a method cannot be computed first and
  read as `Gen.v` is: with an object not yet known, a call on it has every class's method to choose from.
- **The invariant carries over.** `Ghost.v`, `Facts.v`, `Updates.v`, `Inner.v` and `Laws.v` speak of the JDK's
  state and the ghost state; they name `Gen.v` only for what a herd is and for the closure a herd's thread
  runs. Over the trees a herd is a place in the heap whose `threads` field does not change, and that closure
  is the one `denote` makes.
- **What is new work.** What is asked of each closure (`Specs.v`) is a table over `Gen.v`'s closures; over the
  trees a closure is a tree and a scope, and Ox's own must be told from a client's. And each method is proven
  again (`HerdProofs.v`, `ScopeProofs.v`, `ApiProofs.v`, `Main.v`: about a thousand lines), with the steps that
  read fields added, and with the parts `Gen.v` leaves as `extern` or `chaos` (the error mode, a scope's
  finalizers run uninterruptibly) proven for the first time.
