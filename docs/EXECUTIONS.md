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
responded to (`Respond`), anything else an actor does (`Internal`), or nothing (`Stutter`). An `Invocation` is
the method and its arguments, what it is invoked on first. An invocation is responded to with a `Response`:
`Returned(value)` or `Threw(exception)`. What code handles is a `Value`: `Unit`, `Bool`, `Int`, `Str`, or a
`Reference` to an object.

All of this is FrFlow's own DSL: data types, one declared word, and `stated` definitions over it. FrFlow generates
its Rocq as it does any model's (`Types.v`, `Domain/Def_calledBy.v`, …), and nothing in FrFlow's core knows it.
A case named as a type of Rocq's or Lean's prelude is written with a `_` after it there (`Value_Bool_`), as any
such name of a model is.

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

`modules/executions/src/test` has a model with no code (a concurrent set known by its assumptions) checked end to end;
`examples/ox/src/test/scala/ox/threads/ThreadsSuite.scala` checks the model of Ox's threads.

## What is not built

- **Nothing is proven of code yet.** A claim on a method (`onlyStartThreadAdds`) is stated and stands as stated.
  Proving it needs the meaning of an execution of code: the code's trees as programs, calls of what is not the
  code's as events the assumptions describe, and the history as that of an execution of the program.
- **No law of an execution is given.** That a completion follows its call, that an actor's calls are nested, that a call
  nobody calls begins only once handed over: a model that needs one states it as an assumption for now
  (`nothingBeforeTheStart`).
- **No claim of no data race** is generated.
- **Liveness** can be stated (`eventually`, `settles`), and means what it should only over complete, fair executions,
  which nothing yet says the execution is.
- **The old vocabulary of a structure's calls** (`.result`, `.after`, `.in`, `.steps`, `.amongOthers`) is still
  what the sequential examples are written in. It is to go.
