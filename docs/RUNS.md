# Statements about code that takes time

A model of threaded code, or of any code where what holds depends on when, is written with `frflow.runs`
(`modules/runs`). This page says what a statement speaks of, how one is written, how real code is named in it,
and what is built and what is not. `examples/ox/src/main/scala/ox/threads` is a model written this way;
`docs/sketch/ox-threads-model.md` is the fuller model it is growing into.

## A run

A run is the steps taken, one from each moment to the next, each by one actor (a thread). A moment is a number:
how many steps have been taken. A statement is about one arbitrary run, `steps`, a declared word like any other:

```scala
val steps = Declaration[BigInt => Step]("the step taken from each moment of the run")
```

A `Step` is a call made (`Makes`), a call made and completed at once (`Does`), a call completed (`Completes`),
anything else an actor does (`Acts`), or nothing (`Rests`). A call (`Invocation`) is what is called and what it
takes, what it is called on first. A call completes with an `Answer`: `Returned(value)` or `Threw(exception)`.
What code handles, an object or a piece of data, is one type, `Thing`.

All of this is FrFlow's own DSL: data types, one declared word, and `stated` definitions over it. FrFlow generates
its Rocq as it does any model's (`Types.v`, `Domain/Def_calledBy.v`, …), and nothing in FrFlow's core knows it.

## Three kinds of expression

| Kind | Type | Written as |
|---|---|---|
| Looking at what cannot change | `Term[A]`; of an object, `Obj[C]` | `h.field("threads")`, `x + 1`, `live(t, h, w)` |
| Looking at what can change | `Changing[A]`, read with `.at(w)` | `h.field("count").at(w)` |
| Doing | `Call[A]` | `s.add(x)`, `code()`, `supervised(body)` |

- A moment is a `Term[BigInt]` (`World`). Moments are compared with `<` and `<=`.
- An `Obj[C]` says which object, not what is in it. In Rocq every object and piece of data is a `Thing`.
- A word of the model that depends on the moment takes the moment as an argument: `elements(s, w)`.

## What a call has

A `Call[A]` names which calls of the run are meant. `call.by(t)` is those `t` makes.

| Word | Meaning |
|---|---|
| `call.called(w)` | A call is made at `w`. |
| `call.completed(from, answer, to)` | The call made at `from` completes at `to` with `answer`. |
| `call.everyCall((from, answer, to) => p)` | `p` of every completed call. |
| `call.atomic` | Every call completes at the very next moment. |
| `call.calledBefore(w)` | A call was made before `w`. |
| `call.pendingAt(w)` | A call made before `w` has not completed by `w`. |
| `call.calledWithin(from, to)`, `call.completedWithin(from, to)`, `call.returnedWithin(v, from, to)` | Within the two moments. |
| `call.settles(w)` | There is a moment after `w` at which no call is pending. |
| `call.spawned(w)` | The step into `w` hands the call to its actor to run on its own. |
| `outer.calls(inner, w)` | At `w` a pending call of `outer` makes the call `inner` itself. |
| `eventually(w)(later => p)` | `p` at `w` or at some later moment. |

## Real code in a statement

A method, function or constructor applied to the statement's terms is written as the code is, typed against the
real classes, and read as the call it is. It is never run.

```scala
import frflow.{Call as _, *}
import frflow.runs.*
import frflow.runs.InCode.given

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

A model over a run is a `FrModel` like any other: roots, combining claims, and at the bottom the claims on the
code's methods and the assumptions (on the JDK, on who calls the code, on the run itself). `check` asks:

- of each claim with parts, the step from its parts (`<node>_Obl_complete`): proven by hand in the claim's proof
  file, in plain Rocq over the generated definitions;
- of each hand-proven step, that its parts can hold together (`<node>_Obl_feasible`);
- of the model, that what it states at the bottom can hold together (`Whole_Obl_consistent_0`).

A run in which nothing happens meets every statement of the form "after a call, …", so it proves the last two.
That shows the statements do not contradict each other, and no more.

`modules/runs/src/test` has a model with no code (a concurrent set known by its assumptions) checked end to end;
`examples/ox/src/test/scala/ox/threads/ThreadsSuite.scala` checks the model of Ox's threads.

## What is not built

- **Nothing is proven of code yet.** A claim on a method (`onlyStartThreadAdds`) is stated and stands as stated.
  Proving it needs the meaning of a run of code: the code's trees as programs of steps, calls of what is not the
  code's as steps the assumptions describe, and the run as a run of that program.
- **No law of a run is given.** That a completion follows its call, that an actor's calls are nested, that a call
  nobody calls begins only once handed over: a model that needs one states it as an assumption for now
  (`nothingBeforeTheStart`).
- **No claim of no data race** is generated.
- **Liveness** can be stated (`eventually`, `settles`), and means what it should only over complete, fair runs,
  which nothing yet says the run is.
- **The old vocabulary of a structure's calls** (`.result`, `.after`, `.in`, `.steps`, `.amongOthers`) is still
  what the sequential examples are written in. It is to go.
