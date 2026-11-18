# The meaning of Scala's trees, in Rocq

Scala is read into Rocq whole: each TASTy file as the tree the compiler typed (`FrFlow/Scala/Tree.v`), with
nothing chosen in the reading. This page is about the meaning those trees are given. Each tree is given the
program it runs (`FrFlow/Jvm/Prog.v`: it returns, does one operation, loops, or calls a closure), and the
machine of `FrFlow/Jvm/Machine.v` says what a step of a thread may do. The model of Ox's threads
(`docs/EXECUTIONS.md`) is stated over the same programs ("What the proofs are about", below).

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

## Data races

The JVM runs a program as its threads' steps taken one after another only if no such run has a data race: two
threads at the same field or array element, one of them writing, with nothing that orders them (JLS §17.4.5).
A semantics where every field access is one step would let a proof share a plain field between threads through
an invariant, and prove of `x = 1; r1 = y` beside `y = 1; r2 = x` that one of the two reads 1; the JVM lets
both read 0.

So a write is not one step (`FrFlow/Jvm/Machine.v`):

- A write of a field that is not `@volatile`, of a `var` of a method, or of an array element is two operations:
  the thread marks the field as being written (`ObjMark`), then stores the value (`ObjSet`), which takes the
  mark off. The meaning writes every assignment and every initialiser this way; a field's being volatile is
  read from the tree, where the compiler kept the annotation.
- A read or a write of a field that is marked goes wrong.
- A volatile field is written in one step. So is what `Enter` guards: a lazy value, a class being
  initialised. The JVM orders those.

What is checked: the runs of the 25 programs stop with "a data race" if one happens; none does under the four
orders. That no run of Ox's code has one was proven of a herd and of the scope context in a separation logic
over this machine (Iris), which is removed (last at commit 9636ef8, `FrFlow/Jvm/Adequacy.v`,
`examples/ox/rocq/Ox/Proof`): two of its files no longer compiled, and nothing connected it to the model of
Ox's threads. It is to be proven over that model's executions.

What is argued and not proven: that two accesses the JLS calls a race (not ordered by happens-before) can be
brought to overlap in some run of the machine, so that no overlap in any run means no race in the JLS's sense.
That is the standard argument for this way of finding races (RustBelt's non-atomic accesses). It also rests on
the machine's other steps being the JVM's synchronisation actions: a thread's start and join, and the methods
of the JDK's atomics and concurrent collections, each one step by its protocol (`FrFlow/Scala/Jdk.v`).

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

`OxRunSuite` runs each on the JVM, reads the programs' TASTy into trees, and writes `Runs.v`, which says how a
program is run over the programs' trees and Ox's 116, and `Runs1.v` to `Runs4.v`: one lemma for each program,
that under each of four orders of the threads' turns (each thread in turn, and three shuffled orders) every
thread ends and the first gives the number the JVM gave. Rocq proves each by running the meaning
(`vm_compute`): a hundred runs. The lemmas are in four files so that the four are checked at once.

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
| Definitions taken from outside with no meaning | 13 of 184 | 183 of 513 |

The kernel's 13 are a hash code and a serialization proxy the compiler makes for case classes and objects and no
operator calls, `Await.result` (an extension on Scala's futures), and nine of the compiler's own that only a
macro's code uses, when the compiler runs it. Beyond the kernel the meaning is not whole: channels (jox),
flows, reactive streams, input and output and much of Scala's collections have none yet, and a program that
reaches one stops there.

## What the proofs are about

What is proven of Ox is stated over executions (`docs/EXECUTIONS.md`, `examples/ox/README.md`): histories of
events that conform to the same trees, by the same `denote`. In the programs an execution is of, a call of the
JDK is one operation named by the definition called (`FrFlow/Code/Outside.v`), and what it gives is said by the
model's assumptions.

The machine the 25 programs are run on is over those same programs, and writes its run out as an execution
(`FrFlow/Bridge/Frames.v`). A thread is a stack of calls, each with what is left of its program. A call of a method
or a function of the code is an event, the caller waiting under it; a call named by its label is an event too,
and on top of it runs what the library says of the definition (`Library.of_label`), whose steps are the JDK's own
and are no events; an operation on an object of the code is its event; a call that ends responds. So the
comparison with the JVM is of the programs the proofs are about, with the library as what the JDK does, on a
machine whose every step is an event of an execution or none.

That the events such a run writes out are an execution is proven (`FrFlow/Bridge/Executed.v`,
`machine_conforms`): for every table of code, every library of what is outside it, every order of the threads'
turns and every length of run, the events `execute_frames` gives satisfy `Conforms.runs`, the hypothesis every
statement of a model about the code is proven from. It rests on two axioms, `classic` and
`constructive_definite_description`. The proof is in `FrFlow/Bridge`: what one step is (`Steps.v`), what every
step keeps (`Kept.v`), where a call is and that a step takes it there by the rule `Conforms.takes` has for the
step's event (`Stages.v`), the heap and the events that speak of it (`Heap.v`), the laws (`Bridge.v`).

The machine takes a step only where an execution of the code has one, and a run that would take another stops,
saying why (`FrFlow/Bridge/Checks.v`, `Frames.v`). What it checks of a step:

- the arguments of a method or a function of the code are of its parameters' types, what a call gives is of
  the type its signature says, and what a call of the code reads of a field is of the field's class;
- a call runs what each law of `Conforms` that speaks of a call of its label, showing those values, says it
  runs; a call of what is outside the code is one no law speaks of;
- each object an event names is in the heap, of the class it is named with;
- a variable is made with its one field, and read and written there;
- an operation in a call of the code is one that is an event.

None of the 25 programs stops so, under the four orders: their runs took only such steps.

Proving it found two places where `Conforms` said what no run of Ox does, both corrected:

- It said a value of an ordinary class is never a Scala `object`. `supervised` passes `NoErrorMode` where an
  `ErrorMode` is taken, and `unsupervised` passes `NoOpSupervisor`: no run through them was an execution.
  Now the classes above an object the code names are known (`objects`, read with the other facts of the
  classes), and a value of one may be an object. Of any other class it is still assumed that none of its
  values is one: of what calls the code, it is a restriction on how Ox is used.
- It took a call of a method of an object alone of its class to name no object, whether the object has
  state or not. One with state is an object of the heap and the call names it: the law is now of objects
  without state, and the other is a call on an object as any other.

Three things are not proven. The comparison runs are over the whole of Ox with the programs, and are executions
of that code; the model's statements are of the five files it reads, the rest of Ox being outside them: the
theorem holds of that table too, but no run has been made with the rest of Ox as what is outside. That the
machine does what the JVM does is the comparison itself. And that what the model assumes of the JDK holds of
what the library does: it is read against the JDK's documentation and code (`examples/ox/JDK.md`), not
derived.
