# Statements about code that takes time

A model of threaded code, or of any code where what holds depends on when, is written with the module
`modules/executions`: its packages `frflow.values` (what code handles), `frflow.executions` (an execution and the
words of a call) and `frflow.code` (real code written in a statement). This page says what a statement speaks
of, how one is written, how real code is named in it, and what is built and what is not.
`examples/ox/src/main/scala/ox/threads` is a model written this way; `docs/sketch/ox-threads-model.md` is the
fuller model it is growing into.

The names are the literature's: an execution is the Java Language Specification's word for a program as it
runs; its history is a sequence of invocation and response events (Herlihy and Wing); an event that is neither
is internal (nested words), and one in which nothing happens is a stutter (TLA+); what code handles is a value,
a piece of data or a reference to an object (the JVM specification).

## An execution

An execution is the events of a program as it runs, one from each moment to the next, each by one actor (a
thread). A moment is a number: how many events there have been. A statement is about one arbitrary execution,
whose events are `history`, a declared word like any other:

```scala
val history = Declaration[BigInt => Event]("the event at each moment of the execution")
```

An `Event` is a method invoked (`Invoke`), a method invoked and responding at once (`Atomic`), an invocation
responded to (`Respond`), an object of the code made (`Make`), a field of one read (`Read`), a write of one begun
and done (`Mark`, `Write`), what is initialised once asked for (`Enter`), anything else an actor does
(`Internal`), or nothing (`Stutter`). An event of a call says which pending call of its actor makes it (`inside`).
An `Invocation` is the method and its arguments, what it is invoked on first. An invocation is responded to with
a `Response`: `Returned(value)` or `Threw(exception)`. What code handles is a `Value`: `Unit`, `Bool`, `Int`,
`Str`, or a `Reference` to an object.

All of this is FrFlow's own DSL: data types, one declared word, and `stated` definitions over it. FrFlow generates
its Rocq as it does any model's (`Domain/Def_calledBy.v`, …), and nothing in FrFlow's core knows it. The types
have one Rocq text, `FrFlow/Executions.v`, generated from the Scala and kept as generated (`LibrarySuite`): a
model's `Types.v` imports it, so that FrFlow's library can speak of an execution in any model's types. A case
named as a type of Rocq's or Lean's prelude is written with a `_` after it there (`Value_Bool_`), as any such
name of a model is.

## Three kinds of expression

| Kind | Type | Written as |
|---|---|---|
| Looking at what cannot change | `Term[A]`; of an object, `Obj[C]` | `h.field("threads")`, `x + 1`, `live(t, h, w)` |
| Looking at what can change | `Changing[A]`, read with `.at(w)` | `h.field("count").at(w)` |
| Doing | `Call[A]` | `s.add(x)`, `code()`, `supervised(body)` |

- A moment is a `Term[BigInt]` (`World`). Moments are compared with `<` and `<=`.
- An `Obj[C]` says which object, not what is in it. In Rocq every object and piece of data is a `Value`.
- A word of the model that depends on the moment takes the moment as an argument: `elements(s, w)`.

## What a call has

A `Call[A]` names which calls of the execution are meant. `call.by(t)` is those `t` makes.

| Word | Meaning |
|---|---|
| `call.called(w)` | A call is made at `w`. |
| `call.completed(from, response, to)` | The call made at `from` completes at `to` with `response`. |
| `call.everyCall((from, response, to) => p)` | `p` of every completed call. |
| `call.atomic` | Every call completes at the very next moment. |
| `call.calledBefore(w)` | A call was made before `w`. |
| `call.pendingAt(w)` | A call made before `w` has not completed by `w`. |
| `call.calledWithin(from, to)`, `call.completedWithin(from, to)`, `call.returnedWithin(v, from, to)` | Within the two moments. |
| `call.settles(w)` | There is a moment after `w` at which no call is pending. |
| `call.spawned(w)` | The event into `w` spawns the call for its actor, to make on its own. |
| `outer.calls(inner, w)` | At `w` a pending call of `outer` makes the call `inner` itself. |
| `eventually(w)(later => p)` | `p` at `w` or at some later moment. |

## Real code in a statement

A method, function or constructor applied to the statement's terms is written as the code is, typed against the
real classes, and read as the call it is. It is never run.

```scala
import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*

val startIsAtomic = Node.assumption("Starting a thread is atomic.")(
  forall((t: Obj[Thread]) => t.start().atomic))
```

- The call is named by the method's declarer, name and signature, as the tree read from the code's TASTy names
  it (`"java.lang.Thread start :scala.Unit"`): a statement and the code agree on what a method is called.
- What the call takes is the statement's terms and constants in order, what it is called on first.
- Code given by name is written `code.byName` (`h.startThread(code.byName)`); running it is `code()`.
- `call(...)` reads code as a call where no word of a call follows it.
- A field is read by its name: `h.field("threads")` of a `val`, `h.field("count").at(w)` of a `var`. A statement
  may name a field code outside the class may not. To speak of a class private to a package, the model is
  written in that package (`package ox.threads` for `ox.internal.ThreadHerd`).

## A model, and its check

A model over an execution is a `FrModel` like any other: roots, combining claims, and at the bottom the claims on the
code's methods and the assumptions (on the JDK, on who calls the code, on the execution itself). `check` asks:

- of each claim with parts, the step from its parts (`<node>_Obl_complete`): proven by hand in the claim's proof
  file, in plain Rocq over the generated definitions;
- of each hand-proven step, that its parts can hold together (`<node>_Obl_feasible`);
- of the model, that what it states at the bottom can hold together (`Whole_Obl_consistent_0`).

An execution in which nothing happens meets every statement of the form "after a call, …", so it proves the last two.
That shows the statements do not contradict each other, and no more.

`modules/executions/src/test` has a model with no code (a concurrent set known by its assumptions) and a model
of code read from its TASTy (a latch), each checked end to end;
`examples/ox/src/test/scala/ox/threads/ThreadsSuite.scala` checks the model of Ox's threads.

## An execution of code

A model says which code its execution is of. The code is read from its TASTy, as it was compiled, into the trees
the compiler typed; nothing of it is written again:

```scala
val latch: FrModel = FrModel("Latch")(
  enterFindsItOpen, …,
  history.executing(Read.of(classOf[Latch], _.endsWith("latch/Latch.tasty"))))
```

FrFlow then generates, beside the model's statements, the trees (`FrFlowGen/<Model>/Code/<file>.v`) and
`Code.v`: the files, the table of what they define, and `Code_runs history`, "the execution is one of this code".
Every statement that binds `history` takes that as a hypothesis (`o_history_0`), and consistency is asked of an
execution of the code.

What it is for an execution to be one of some code is said once, in FrFlow's Rocq library, for any trees
(`FrFlow/Code/Conforms.v`), over the meaning of the trees (`FrFlow/Scala/Meaning.v`):

- A call of a method of the code on an object the code made, or of a function the code wrote, is made by one
  actor. The events that actor makes directly inside the call are the steps of the method's program, in order:
  an object made, a field read or written, a call made and its response. Other actors' events, and what happens
  inside the calls it makes, come between; nothing is said of how they interleave.
- A call of what is outside the code (the JDK, a class not read) is an event with any response of its type.
  What it gives is what the model assumes of it, in the model's own words (`getGivesTheFlag`).
- The execution's values name the code's: each at most one, numbers, texts and truth values themselves.
- Code whose meaning is not given (`Chaos`) may make any event: a proof passes it only where it is not reached.

A claim of the code is then a claim with parts like any other: its parts are the assumptions it needs, and its
step is proven in its proof file, by walking the method's program along the events of a call (`FrFlow/Code/Walk.v`:
`walk` computes what the program does next, `step_read`, `step_called`, `step_method` say what event that is).
`enterReadsItOpen` is proven so of `Latch.enter`'s tree; `startThreadReadsTheFlagUnset`,
`closingSetsTheFlagItself` and `theForkFunctionRemovesTheCurrentThread` of Ox's `ThreadHerd`, as its jar has it
(`examples/ox/rocq/Proofs/OxThreads`). The last walks a function the code wrote: the one `startThread` hands the
thread factory, known to be the code's by finding its tree among the trees read.

What a model must still say itself, as assumptions:

- that a method is called only on an object the code made (`l.isMade(w)`): the JVM's type safety, where nothing
  outside the code extends the class;
- that a `val` is read as what it holds (`l.readsAsHeld("closed")`);
- what each method of the JDK it speaks of does.

## What is not built

- **Who else touches what a class keeps to itself.** That only a class's own methods call methods on an object it
  holds in a private field is not derived from the trees: a model states it as an assumption. With capture
  checking it is what the compiler would say.
- **What the heap holds.** A read of a `var` is an event with any value of the field's type: that it finds what
  was last written is not said, so a claim that needs the value of a local variable across calls (the end of a
  loop that other threads' functions write to) is not proven of the code.
- **A method of what is outside taking an argument by name** is read as taking it evaluated.
- **No law of an execution is given.** That a completion follows its call, that an actor's calls are nested, that
  a call nobody calls begins only once handed over: a model that needs one states it as an assumption.
- **No claim of no data race** is generated.
- **Liveness** can be stated (`eventually`, `settles`), and means what it should only over complete, fair
  executions, which nothing yet says the execution is.
- **The old vocabulary of a structure's calls** (`.result`, `.after`, `.in`, `.steps`, `.amongOthers`) is still
  what the sequential examples are written in. It is to go.
