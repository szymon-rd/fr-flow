# Ox threads: the model, as a sketch

Status: a sketch to iterate on. Nothing here is compiled or run.
The Scala is Ox's own code, unchanged (`ThreadHerd.scala`, `unsupervised.scala`, `fork.scala`, `supervised.scala`).

The vocabulary is now built, with differences from section 0 (`docs/EXECUTIONS.md` says it as built: a run is
called an execution and its steps events, a moment is a number, an object is an `Obj[C]`, a word that depends on
the moment takes it as an argument). The herd's part of
the safety tree (roots A and B at the level of a herd) is a real model, checked by FrFlow with its steps proven:
`examples/ox/src/main/scala/ox/threads`. Proving it changed three statements, which this sketch does not yet
show: the code runs before the fork leaves at every moment of the run, closing is the owner's, and a caller of
startThread neither closes the herd nor leaves its set.

The model's execution is now one of `ThreadHerd` as Ox's jar has it, read from its TASTy
(`docs/EXECUTIONS.md`, "An execution of code"). Two claims of the code are proven of its tree, by FrFlow's
check: that `startThread` adds a thread, or returns, only after it has read the herd's flag as unset
(`startThreadReadsTheFlagUnset`), and that closing, by the herd's owner, completes only after it has set the
flag (`closingSetsTheFlagItself`). With what is assumed of an atomic boolean they give the third root. A third: the
function `startThread` hands the thread factory removes from the herd's set only the thread that
`Thread.currentThread()` gave it (`theForkFunctionRemovesTheCurrentThread`); with the assumption that only such
a function removes from the set (what capture checking would say), a fork is removed only by itself. A fourth:
a call of startThread that itself adds a thread is pending when it does (`startThreadAddsWhileItRuns`: a call of
the code makes no event of its own once it has responded); with the assumption that only startThread adds to
the set, a thread is added only during a call of startThread. A fifth and sixth: the thread startThread adds is
the one its factory returned to it (`startThreadAddsWhatItsFactoryMade`), and it adds before it starts one
(`startThreadAddsBeforeItStarts`); with the assumption that a thread a factory made for a call of startThread is
started only by that call (`onlyItsMakerStartsAThread`), an added thread has not been started. A seventh, of
closing's `while` loop: closing completes only after a call it made asking whether the herd's set is empty was
answered yes (`closingEndsOnceFoundEmpty`, by the loop rule: every turn asks, and only a yes leaves the loop);
with what is assumed of `isEmpty`, closing ends on an empty set. It rests on a claim not yet proven of the code,
that the two traversals closing makes do not throw (`closingsTraversalsReturn`), and on the JDK's `set` and
`isEmpty` not throwing. That the flag stays set (`theFlagStaysSet`) now follows from three parts: what an atomic
boolean holds changes only after a call that sets it so (assumed of the JDK), a herd's flag is set only by a call
of closing itself (assumed: what capture checking would say), and closing sets it only to true
(`closingSetsTheFlagOnlyToTrue`, a claim of the code not yet proven: past its loop closing reads a local variable
and may throw what it holds, and what a local variable holds is not yet said of an execution). Still stated and
not proven of the code: that a caller of startThread neither closes nor leaves, when the code a fork
was made to run is called (`codeRunsBeforeLeaving`), that closing's traversals do not throw, and that closing
sets the flag only to true. The scopes above the herd and liveness are not in the model.

## The tree

### Safety: what never happens

```
A  noForkRunsAfterItsScope            After a scope has completed, no fork of it runs its code.
├─ closedScopeIsEmptyForGood          After closing has completed, every fork has left and no thread is added.
│  ├─ closingEndsOnEmpty              local   ThreadHerd            <- isEmptyIsExact, joinReturnsOrIsInterrupted,
│  │                                                                  forEachThrowsOnlyWhatItsFunctionDoes, theseJdkCallsReturn
│  ├─ liveForksAreInTheSet            A fork that has not left is in the set.
│  │                                                               <- addPutsItIn, removeTakesOnlyItOut, setCallsAreAtomic
│  └─ nothingIsAddedOnceEmpty         Once the set is empty after closing was called, no thread is added.
│     ├─ startThreadCallersStayInside While a thread calls startThread, it is inside the scope.
│     │  ├─ forksAreMadeFromInside    ASSUMPTION about Ox's callers
│     │  ├─ onlyForksCallStartThread  local   fork.scala
│     │  ├─ aForkRemovesOnlyItself    local   ThreadHerd            <- currentThreadIsTheCaller
│     │  ├─ codeRunsBeforeLeaving     local   ThreadHerd
│     │  └─ closingIsCalledAtTheScopesEnd  local   unsupervised.scala
│     ├─ onlyStartThreadAdds          local   ThreadHerd            <- newThreadIsUnstarted
│     └─ liveForksAreInTheSet
├─ scopeEndsAfterClosing              local   unsupervised.scala
├─ scopesAreRunOnceByTheirOwner       local   supervised.scala, unsupervised.scala
└─ codeRunsBeforeLeaving              local   ThreadHerd            <- firstStartSpawnsTheBody, startIsAtomic,
                                                                      newThreadIsUnstarted, currentThreadIsTheCaller

B  noForkIsMadeAfterItsScope          After a scope has completed, no fork is made in it.
├─ closedScopeIsEmptyForGood
├─ scopeEndsAfterClosing
└─ scopesAreRunOnceByTheirOwner

R  aLateForkIsRefused                 A fork attempted after its scope has completed throws and adds no thread.
├─ closedHerdRefusesToStart           (rests on no assumption about callers)
│  ├─ closingSetsTheFlag              local   ThreadHerd            <- setStores, atomicsAreAtomic
│  ├─ theFlagStaysSet                 local   ThreadHerd            <- setStores
│  ├─ startThreadFirstSeesTheFlagUnset  local ThreadHerd            <- getReads
│  └─ onlyStartThreadAdds
├─ scopeEndsAfterClosing
├─ scopesAreRunOnceByTheirOwner
└─ forkReturnsOnlyIfStartThreadDid    local   fork.scala

C  supervisedReturnsOnlyOnSuccess     supervised returns a value only if its body returned it and, at some
│                                     moment after, every user fork then made in its scope had succeeded.
├─ supervisedReturnsItsBodyForksJoin  local   supervised.scala
├─ joinReturnsWhatTheCodeReturned     local   fork.scala            <- firstCompletionStays, getAnswersTheOutcome
├─ successIsReportedAtZero            local   supervised.scala      <- decrementTakesOne, atomicsAreAtomic
└─ countIsPositiveWhileAUserForkHasNotSucceeded   local supervised.scala, fork.scala   <- incrementAddsOne
```

### Liveness: what does happen

```
D  aScopeCompletesAfterItsBody        Once the body of a scope has completed, the scope completes.
├─ closingCompletes                   A call of closing by the herd's owner completes.
│  ├─ theSetEmptiesForGood            While closing is pending, there is a moment from which the set stays empty.
│  │  ├─ everyLiveForkIsInterrupted   While closing is pending, a fork that stays in the set is interrupted.
│  │  │  ├─ closingKeepsGoing
│  │  │  ├─ closingPassesAndAsksAgain          local   ThreadHerd   <- forEachCompletes, interruptIsAtomic
│  │  │  ├─ aPassOfClosingInterruptsWhatStays  local   ThreadHerd   <- forEachReachesWhatStays
│  │  │  └─ liveForksAreInTheSet
│  │  ├─ anInterruptedForkLeaves      A fork that has been interrupted leaves.
│  │  │  ├─ forkCodeStopsWhenInterrupted       ASSUMPTION about the user's code
│  │  │  ├─ startThreadStartsWhatItAdds        local   ThreadHerd
│  │  │  ├─ aStartedForkCallsItsCode           local   ThreadHerd   <- firstStartSpawnsTheBody, aStartedThreadRuns
│  │  │  ├─ forkCodeCompletesOnceTheUsersDoes  local   fork.scala
│  │  │  └─ aForkLeavesOnceItsCodeCompletes    local   ThreadHerd
│  │  ├─ noThreadIsAddedForever       Once the flag is set, from some moment on no thread is added.
│  │  │  ├─ startThreadFirstSeesTheFlagUnset
│  │  │  ├─ theFlagStaysSet
│  │  │  └─ onlyStartThreadAdds
│  │  └─ onlyLiveForksAreInTheSet     Whatever is in the set is a fork that has not left.
│  │                                                               <- addPutsItIn, removeTakesOnlyItOut
│  ├─ closingKeepsGoing               A pending closing completes or asks again whether the set is empty.
│  │  ├─ closingAsksWhetherTheSetIsEmpty       local   ThreadHerd
│  │  ├─ closingPassesAndAsksAgain
│  │  ├─ closingCompletesWhenAnsweredEmpty
│  │  └─ aJoinInClosingCompletes      A join that closing makes completes.
│  │     ├─ closingJoinsOnlyInterruptedForks   local   ThreadHerd   <- forEachGivesOnlyElements
│  │     ├─ anInterruptedForkLeaves
│  │     └─ aForkThatHasLeftFinishes           local   ThreadHerd   <- joinCompletesOnceFinished
│  └─ closingCompletesWhenAnsweredEmpty        local   ThreadHerd   <- isEmptyIsExact
├─ theScopeGoesOnAfterItsBody         local   unsupervised.scala
├─ runFinalizersCompletes             local   unsupervised.scala    <- ASSUMPTION finalizersComplete
└─ scopesAreRunOnceByTheirOwner

E  aFailedForkEndsSupervised          Once the code of a fork of a supervised scope has thrown, supervised completes.
├─ aThrowingForkReports               local   fork.scala
├─ aSupervisorToldOfAnExceptionHasAReport  local   supervised.scala <- firstCompletionStays, completingIsAtomic
├─ theBodyOfASupervisedScopeCompletesOnceReported
│  ├─ supervisedsBodyOnlyWaitsForTwoJoins  local   supervised.scala <- getCompletesOnceThereIsAnOutcome
│  ├─ successIsReportedAtZero
│  └─ countIsPositiveWhileAUserForkHasNotSucceeded
├─ aScopeCompletesAfterItsBody        (D)
└─ supervisedCompletesOnceItsScopeDoes     local   supervised.scala <- forEachCompletes

F  supervisedCompletesOnSuccess       Once every user fork made in a supervised scope has reported success, with
│                                     none being made, supervised completes.
├─ countIsZeroOnceAllUserForksSucceeded    local   supervised.scala, fork.scala
├─ aDecrementToZeroReportsSuccess          local   supervised.scala <- firstCompletionStays
├─ theBodyOfASupervisedScopeCompletesOnceReported
├─ aScopeCompletesAfterItsBody        (D)
└─ supervisedCompletesOnceItsScopeDoes
```

What the sketch shows:

- **A and B rest on three things:** the herd's set, an exact `isEmpty`, and callers staying inside the scope.
  `join`, `interrupt` and `forEach` matter to them only in what they may throw: closing must not be thrown out of
  its loop.
- **The flag gives a separate guarantee (R)** that needs no assumption about callers. In liveness it does a second
  job: it is why forks stop being added, so closing can end.
- **What `join`, `interrupt` and `forEach` do enters only through liveness (D).**
- **Liveness needs two assumptions about the user's code:** a fork's code stops once its thread is interrupted, and
  finalizers complete. Without the first, no scope with a fork can be shown to end.
- **"A fork has finished" cannot mean "its thread has finished".** Closing leaves when the set is empty, and a
  thread takes itself out of the set a few steps before it ends. The claims are about the fork's code.
- **A scope is identified by its herd.** Ox makes copies of a capability (`asNoErrorMode`); all share the herd.

## 0. Words used (FrFlow, to be built)

A run is a sequence of moments. Between two consecutive moments one actor (a thread) takes one step.

### Steps

A claim never names a step, but what a step is decides what "every run" covers. A step is one of:

- an atomic call of a JDK method;
- the making, or the completing, of a call that is not atomic;
- one read or one write of a field, a `var` or an array element by real code.

Code between two steps of a thread touches nothing another thread can see. A run is any interleaving of the
threads' steps, so a claim holds under every schedule. Other threads can act between any two steps of Ox's code:
between the check of the flag and the adding of a thread, for example.

A JDK call may answer anything its assumptions do not exclude. So a call that waits may throw
`InterruptedException` at any moment, and no claim depends on when a thread is interrupted.

| Primitive | Meaning |
|---|---|
| `World`, `a.before(b)` | A moment of a run; `a` is earlier than `b` in the same run. |
| `x.at(w)` | The value of something that changes, at a moment. |
| `call.by(who)` | The actor that makes the call; omitted means any. |
| `call.called(w)` | The call is made at `w`. |
| `call.completed(from, answer, to)` | The call made at `from` completes at `to` with `answer`. |
| `call.spawned(w)` | At `w` the call is given to its actor to run concurrently. |
| `outer.calls(inner, w)` | At `w` a pending call `outer` makes the call `inner` itself, not through another call. |

| Defined from them | Meaning |
|---|---|
| `call.everyCall((from, answer, to) => p)` | `p` for every completed call. |
| `call.atomic` | Every call completes at the very next moment. |
| `call.calledBefore(w)` | A call was made before `w`. |
| `call.pendingAt(w)` | A call was made before `w` and has not completed by `w`. |
| `call.calledWithin(from, to)` | A call was made at a moment from `from` to `to`. |
| `call.returnedWithin(v, from, to)` | A call made and completed from `from` to `to` returned `v`. |
| `call.settles(w)` | There is a moment after `w` at which no call of it is pending. |
| `a.notAfter(b)` | `a` is `b` or earlier. |
| `w.eventually(later => p)` | `p` at `w` or at some later moment. |

`answer` is `Returned(v)` or `Threw(e)`.

### Three kinds of expression

What an expression is depends on whether anything happens, and whether the moment matters.

| Kind | Type | What it is | Written as |
|---|---|---|---|
| Looking at what cannot change | `Term[A]` | a variable, a `val` field, an operation on data, a constant word of the model, a defined word | `h.threads`, `x + 1`, `body(t)`, `live(t, h, w)` |
| Looking at what can change | `Changing[A]`, read with `.at(w)` | a `var` field, a word of the model declared `Changing` | `elements(s).at(w)` |
| Doing | `Call[A]` | a method, function or constructor of real code, applied | `s.add(x)`, `code()`, `supervised(body)` |

- **Real code applied is always a `Call`,** also when it is pure. It is never a value: `s.add(x) === true` does not
  typecheck. Its value is reached through `everyCall`.
- **A word of the model applied is never a `Call`.** A `Declaration` says in its type whether it changes. A defined
  word that speaks of a moment takes the moment as an ordinary argument.
- **Pure code becomes a value by being given to a word of the model,** as in FrFlow today (`define`, `lifted`).

Rules of the model (not nodes):

1. **Frame.** A step changes only the words its assumption or its code names.
2. **Spawning.** A call that no code calls begins only after it was spawned, once.
3. **Nesting.** A call an actor makes during another of its calls completes first.
4. **Closed JDK.** A JDK method calls only what its assumptions say.
5. **Complete runs.** A run goes on for as long as some actor can take a step.
6. **Progress.** A thread that is running code, and is not waiting inside a JDK call, takes its next step.
7. **Finitely many actors** exist at any moment.

Rules 5 to 7 are what liveness adds. Rule 6 is an assumption about the scheduler.

## 1. The JVM: assumptions on its methods

```scala
type KeySet[A] = ConcurrentHashMap.KeySetView[A, java.lang.Boolean]

// Words of the model for JDK types. They are not JDK members.
def elements[A] = Declaration[KeySet[A] => Changing[Set[A]]]("what is in the set")
val flag        = Declaration[AtomicBoolean => Changing[Boolean]]("what the atomic boolean holds")
val count       = Declaration[AtomicInteger => Changing[Int]]("what the atomic integer holds")
def outcome[A]  = Declaration[CompletableFuture[A] => Changing[Option[Answer[A]]]]("what the future was completed with")
val body        = Declaration[Thread => Runnable]("the code the thread was made to run")

/** The thread has finished: it has run its body to the end. */
val finished = define { (t: Term[Thread], w: World) =>
  body(t).run().by(t).calledBefore(w) && !body(t).run().by(t).pendingAt(w) }
```

### Concurrent sets

```scala
val setCallsAreAtomic = Node.assumption(
  "Adding to a concurrent set, removing from it and asking whether it is empty are each atomic.")(
  forall([A] => (s: Term[KeySet[A]], x: Term[A]) => s.add(x).atomic && s.remove(x).atomic && s.isEmpty().atomic))

val addPutsItIn = Node.assumption("Adding an element puts it in the set.")(
  forall([A] => (s: Term[KeySet[A]], x: Term[A]) =>
    s.add(x).everyCall((from, answer, to) => elements(s).at(to) === elements(s).at(from) + x)))

val removeTakesOnlyItOut = Node.assumption("Removing an element takes that element out of the set, and no other.")(
  forall([A] => (s: Term[KeySet[A]], x: Term[A]) =>
    s.remove(x).everyCall((from, answer, to) => elements(s).at(to) === elements(s).at(from) - x)))

// More than the JDK promises: this set sums its size without a lock.
val isEmptyIsExact = Node.assumption("Asking a set whether it is empty answers whether it is empty at that moment.")(
  forall([A] => (s: Term[KeySet[A]]) =>
    s.isEmpty().everyCall((from, answer, to) => answer === Returned(elements(s).at(from).isEmpty))))

val forEachThrowsOnlyWhatItsFunctionDoes = Node.assumption("forEach throws only what a call of its function threw.")(
  forall([A] => (s: Term[KeySet[A]], f: Term[Consumer[A]], c: Term[Thread], e: Term[Throwable]) =>
    s.forEach(f).by(c).everyCall((from, answer, to) =>
      (answer === Threw(e)) implies exists((x: Term[A], a: World, b: World) =>
        s.forEach(f).by(c).calls(f.accept(x), a) && f.accept(x).by(c).completed(a, Threw(e), b)))))

// The three below are used only by liveness.
val forEachGivesOnlyElements = Node.assumption("forEach calls its function only on elements that have been in the set.")(
  forall([A] => (s: Term[KeySet[A]], f: Term[Consumer[A]], x: Term[A], w: World) =>
    s.forEach(f).calls(f.accept(x), w) implies
      exists((m: World) => m.notAfter(w) && elements(s).at(m).contains(x))))

val forEachReachesWhatStays = Node.assumption(
  "forEach calls its function on every element that is in the set throughout the call.")(
  forall([A] => (s: Term[KeySet[A]], f: Term[Consumer[A]], x: Term[A], c: Term[Thread]) =>
    s.forEach(f).by(c).everyCall((from, answer, to) =>
      forall((m: World) => (from.notAfter(m) && m.notAfter(to)) implies elements(s).at(m).contains(x)) implies
        f.accept(x).by(c).calledWithin(from, to))))

val forEachCompletes = Node.assumption("forEach completes once every call it makes of its function has completed.")(
  forall([A] => (s: Term[KeySet[A]], f: Term[Consumer[A]], c: Term[Thread], w: World) =>
    (s.forEach(f).by(c).pendingAt(w) &&
      forall((x: Term[A], a: World) => s.forEach(f).by(c).calls(f.accept(x), a) implies f.accept(x).by(c).settles(a)))
      implies s.forEach(f).by(c).settles(w)))
```

### Threads

```scala
val startIsAtomic = Node.assumption("Starting a thread is atomic.")(
  forall((t: Term[Thread]) => t.start().atomic))

val firstStartSpawnsTheBody = Node.assumption("Starting a thread for the first time gives the thread its body to run.")(
  forall((t: Term[Thread]) =>
    t.start().everyCall((from, answer, to) =>
      !t.start().calledBefore(from) implies body(t).run().by(t).spawned(to))))

val currentThreadIsTheCaller = Node.assumption("Asking for the current thread answers the thread that asks.")(
  forall((t: Term[Thread]) =>
    Thread.currentThread().by(t).everyCall((from, answer, to) => answer === Returned(t))))

// Ox's factory can be replaced by the user: this is assumed of whichever is used.
val newThreadIsUnstarted = Node.assumption(
  "A thread factory answers a thread that has not been started, whose body is the code it was given.")(
  forall((factory: Term[ThreadFactory], r: Term[Runnable], t: Term[Thread]) =>
    factory.newThread(r).everyCall((from, answer, to) =>
      (answer === Returned(t)) implies ((body(t) === r) && !t.start().calledBefore(to)))))

val joinReturnsOrIsInterrupted = Node.assumption("Joining a thread returns, or throws InterruptedException.")(
  forall((t: Term[Thread]) =>
    t.join().everyCall((from, answer, to) =>
      (answer === Returned(())) || exists((e: Term[InterruptedException]) => answer === Threw(e)))))

// Out of memory and the like are left out: see section 7.
val theseJdkCallsReturn = Node.assumption(
  "Adding to a set, removing from it, starting a thread for the first time and interrupting a thread return.")(
  forall([A] => (s: Term[KeySet[A]], x: Term[A], t: Term[Thread]) =>
    s.add(x).everyCall((from, answer, to) => exists((r: Term[Boolean]) => answer === Returned(r))) &&
    s.remove(x).everyCall((from, answer, to) => exists((r: Term[Boolean]) => answer === Returned(r))) &&
    t.start().everyCall((from, answer, to) => !t.start().calledBefore(from) implies (answer === Returned(()))) &&
    t.interrupt().everyCall((from, answer, to) => answer === Returned(()))))

// The three below are used only by liveness.
val aStartedThreadRuns = Node.assumption("A thread that was given its body to run eventually runs it.")(
  forall((t: Term[Thread], w: World) =>
    body(t).run().by(t).spawned(w) implies w.eventually(later => body(t).run().by(t).calledBefore(later))))

val joinCompletesOnceFinished = Node.assumption("Joining a thread completes once the thread has finished.")(
  forall((t: Term[Thread], w: World) =>
    (t.join().pendingAt(w) && finished(t, w)) implies t.join().settles(w)))

val interruptIsAtomic = Node.assumption("Interrupting a thread is atomic.")(
  forall((t: Term[Thread]) => t.interrupt().atomic))
```

### Atomics

```scala
val atomicsAreAtomic = Node.assumption("Reading, writing, incrementing and decrementing an atomic are each atomic.")(
  forall((b: Term[AtomicBoolean], v: Term[Boolean], i: Term[AtomicInteger]) =>
    b.get().atomic && b.set(v).atomic && i.incrementAndGet().atomic && i.decrementAndGet().atomic))

val setStores = Node.assumption("Writing an atomic boolean makes it hold what was written.")(
  forall((b: Term[AtomicBoolean], v: Term[Boolean]) =>
    b.set(v).everyCall((from, answer, to) => flag(b).at(to) === v)))

val getReads = Node.assumption("Reading an atomic boolean answers what it holds.")(
  forall((b: Term[AtomicBoolean]) =>
    b.get().everyCall((from, answer, to) => answer === Returned(flag(b).at(from)))))

val incrementAddsOne = Node.assumption("Incrementing an atomic integer adds one and answers the new value.")(
  forall((i: Term[AtomicInteger]) =>
    i.incrementAndGet().everyCall((from, answer, to) =>
      (count(i).at(to) === count(i).at(from) + 1) && (answer === Returned(count(i).at(to))))))

val decrementTakesOne = Node.assumption("Decrementing an atomic integer takes one off and answers the new value.")(
  forall((i: Term[AtomicInteger]) =>
    i.decrementAndGet().everyCall((from, answer, to) =>
      (count(i).at(to) === count(i).at(from) - 1) && (answer === Returned(count(i).at(to))))))
```

### Futures

```scala
val completingIsAtomic = Node.assumption("Completing a future, with a value or an exception, is atomic.")(
  forall([A] => (f: Term[CompletableFuture[A]], v: Term[A], e: Term[Throwable]) =>
    f.complete(v).atomic && f.completeExceptionally(e).atomic))

// The same is assumed of completeExceptionally, with Threw(e).
val firstCompletionStays = Node.assumption(
  "Completing a future keeps the outcome it already has, and answers whether it had none.")(
  forall([A] => (f: Term[CompletableFuture[A]], v: Term[A]) =>
    f.complete(v).everyCall((from, answer, to) =>
      (outcome(f).at(to) === some(outcome(f).at(from).getOrElse(Returned(v)))) &&
      (answer === Returned(outcome(f).at(from).isEmpty)))))

val getAnswersTheOutcome = Node.assumption("Getting from a future returns a value only if it was completed with it.")(
  forall([A] => (f: Term[CompletableFuture[A]], v: Term[A]) =>
    f.get().everyCall((from, answer, to) =>
      (answer === Returned(v)) implies (outcome(f).at(to) === some(Returned(v))))))

// Used only by liveness.
val getCompletesOnceThereIsAnOutcome = Node.assumption("Getting from a future completes once the future has an outcome.")(
  forall([A] => (f: Term[CompletableFuture[A]], w: World) =>
    (f.get().pendingAt(w) && outcome(f).at(w).isDefined) implies f.get().settles(w)))
```

## 2. Ox: the words of the model

A scope is named by its herd `h`. Every word is defined from calls of Ox's own code.

```scala
// Abbreviations, plain Scala.
def closing(h: Term[ThreadHerd]) = h.interruptAllAndJoinUntilCompleted()
def ownerClosing(h: Term[ThreadHerd]) = closing(h).by(h.herdOwner)
def ownerAsking(h: Term[ThreadHerd]) = h.threads.isEmpty().by(h.herdOwner)

/** The thread is a fork of the scope: the herd has added it to its set. */
val forkOf = define { (t: Term[Thread], h: Term[ThreadHerd], w: World) => h.threads.add(t).calledBefore(w) }

/** The fork has left: it has taken itself out of the set. */
val left = define { (t: Term[Thread], h: Term[ThreadHerd], w: World) => h.threads.remove(t).calledBefore(w) }

/** The fork has not left. */
val live = define { (t: Term[Thread], h: Term[ThreadHerd], w: World) => forkOf(t, h, w) && !left(t, h, w) }

/** The fork was made to run this code: its thread was added during `startThread(code)`, by its caller. */
val madeToRun = define { (t: Term[Thread], h: Term[ThreadHerd], code: Term[() => Unit], w: World) =>
  exists((c: Term[Thread], m: World) =>
    m.before(w) && h.threads.add(t).by(c).called(m) && h.startThread(code).by(c).pendingAt(m)) }

/** The fork was made for this code of the user's: its thread was added during a fork function called with it. */
val forkFor = define { [T] => (t: Term[Thread], h: Term[ThreadHerd], user: Term[() => T], w: World) =>
  exists((ox: Term[Ox], c: Term[Thread], m: World) =>
    (ox.herd === h) && m.before(w) && h.threads.add(t).by(c).called(m) &&
    (fork(user)(using ox).by(c).pendingAt(m) || forkUser(user)(using ox).by(c).pendingAt(m))) }

/** The thread is a user fork of the scope: it was added during a call of `forkUser` with the scope's capability. */
val userFork = define { (u: Term[Thread], h: Term[ThreadHerd], w: World) =>
  exists([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread], m: World) =>
    (ox.herd === h) && m.before(w) && h.threads.add(u).by(c).called(m) && forkUser(user)(using ox).by(c).pendingAt(m)) }

/** Closing the herd, by its owner, has completed. */
val closed = define { (h: Term[ThreadHerd], w: World) =>
  ownerClosing(h).calledBefore(w) && !ownerClosing(h).pendingAt(w) }

/** The scope has been opened: `scopedWithCapability` was called with a capability of this herd. */
val opened = define { (h: Term[ThreadHerd], w: World) => exists([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
  (ox.herd === h) && scopedWithCapability(ox)(f).calledBefore(w)) }

/** The scope is running. */
val running = define { (h: Term[ThreadHerd], w: World) => exists([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
  (ox.herd === h) && scopedWithCapability(ox)(f).pendingAt(w)) }

/** The scope has completed. */
val done = define { (h: Term[ThreadHerd], w: World) => opened(h, w) && !running(h, w) }

/** The body the scope was run with has completed. */
val bodyDone = define { [T] => (ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
  f(using ox).by(ox.herd.herdOwner).calledBefore(w) && !f(using ox).by(ox.herd.herdOwner).pendingAt(w) }

/** The thread is inside the scope: its owner before closing is called, or a fork of it that has not left. */
val inside = define { (c: Term[Thread], h: Term[ThreadHerd], w: World) =>
  ((c === h.herdOwner) && running(h, w) && !closing(h).calledBefore(w)) || live(c, h, w) }

/** A call of `supervised` by `o` runs this scope, with this body of Ox's making. */
val supervisedRuns = define { [T] => (body: Term[Ox ?=> T], o: Term[Thread], ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
  exists((a: World) =>
    a.before(w) && supervised(body).by(o).pendingAt(a) && scopedWithCapability(ox)(f).by(o).called(a)) }

/** The user fork has reported success to the supervisor. */
val reportedSuccess = define { (u: Term[Thread], ox: Term[Ox], w: World) =>
  ox.supervisor.forkSuccess().by(u).calledBefore(w) && !ox.supervisor.forkSuccess().by(u).pendingAt(w) }

/** No user fork of the scope is being made, and no attempt to make one has failed. */
val noUserForkInTheMaking = define { (h: Term[ThreadHerd], w: World) =>
  !exists([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread]) =>
    (ox.herd === h) && (forkUser(user)(using ox).by(c).pendingAt(w) ||
      exists((a: World, e: Term[Throwable], b: World) =>
        b.notAfter(w) && forkUser(user)(using ox).by(c).completed(a, Threw(e), b)))) }
```

`fork` and `forkUser` stand for `forkError` and `forkUserError`, which they call. `ox.supervisor.running` and
`ox.supervisor.result` are those of the `DefaultSupervisor` a supervised scope has.

## 3. Ox: what is assumed of its callers

```scala
// With capture checking this would be what the compiler says, not an assumption.
val forksAreMadeFromInside = Node.assumption(
  "A fork is made in a scope only by a thread inside it: its owner before closing, or a fork of it that has not left.")(
  forall([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread], w: World) =>
    (fork(user)(using ox).by(c).called(w) || forkUser(user)(using ox).by(c).called(w)) implies
      inside(c, ox.herd, w)))

// The two below are used only by liveness.
val forkCodeStopsWhenInterrupted = Node.assumption(
  "The code given to a fork completes once its thread has been interrupted.")(
  forall([T] => (h: Term[ThreadHerd], t: Term[Thread], user: Term[() => T], w: World) =>
    (forkFor(t, h, user, w) && user().by(t).pendingAt(w) && t.interrupt().calledBefore(w)) implies
      user().by(t).settles(w)))

val finalizersComplete = Node.assumption("A finalizer registered with a scope completes whenever it is called.")(
  forall((ox: Term[Ox], g: Term[() => Unit], w: World) =>
    (ox.addFinalizer(g).calledBefore(w) && g().pendingAt(w)) implies g().settles(w)))
```

## 4. Ox: local claims, each provable from one piece of code and the JVM assumptions

### `ThreadHerd.scala`, safety

```scala
val onlyStartThreadAdds = Node.claim(
  "A thread is added to a herd's set only during a call of startThread, by its caller, and has not been started.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], c: Term[Thread], w: World) =>
    h.threads.add(t).by(c).called(w) implies
      (exists((code: Term[() => Unit]) => h.startThread(code).by(c).pendingAt(w)) && !t.start().calledBefore(w))))

val aForkRemovesOnlyItself = Node.claim("A thread is removed from a herd's set only by itself.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], c: Term[Thread], w: World) =>
    h.threads.remove(t).by(c).called(w) implies (c === t)))

val codeRunsBeforeLeaving = Node.claim(
  "A fork calls the code it was made to run only before it leaves, and leaves only when no such call is pending.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], code: Term[() => Unit], w: World) =>
    madeToRun(t, h, code, w) implies
      ((code().by(t).called(w) implies !left(t, h, w)) &&
       (h.threads.remove(t).called(w) implies !code().by(t).pendingAt(w)))))

val closingEndsOnEmpty = Node.claim(
  "Closing a herd completes only after a moment, during it, at which the herd's set is empty.")(
  forall((h: Term[ThreadHerd]) =>
    ownerClosing(h).everyCall((from, answer, to) =>
      exists((m: World) => from.before(m) && m.notAfter(to) && elements(h.threads).at(m).isEmpty))))

val closingSetsTheFlag = Node.claim("When closing a herd completes, the herd's flag is set.")(
  forall((h: Term[ThreadHerd]) =>
    ownerClosing(h).everyCall((from, answer, to) => flag(h.shutdownInProgress).at(to))))

val theFlagStaysSet = Node.claim("Once a herd's flag is set, it stays set.")(
  forall((h: Term[ThreadHerd], a: World, b: World) =>
    (a.before(b) && flag(h.shutdownInProgress).at(a)) implies flag(h.shutdownInProgress).at(b)))

val startThreadFirstSeesTheFlagUnset = Node.claim(
  "startThread adds a thread, or returns, only after it has seen the herd's flag unset.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], t: Term[Thread], from: World, w: World) =>
    (h.startThread(code).by(c).called(from) && from.before(w) &&
      (h.threads.add(t).by(c).called(w) || h.startThread(code).by(c).completed(from, Returned(()), w))) implies
      exists((m: World) => from.notAfter(m) && m.before(w) && !flag(h.shutdownInProgress).at(m))))

// The two below are used only by liveness.
val closingJoinsOnlyInterruptedForks = Node.claim(
  "Closing joins a thread only if it is a fork of the herd that has been interrupted.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    (ownerClosing(h).pendingAt(w) && t.join().by(h.herdOwner).called(w)) implies
      (forkOf(t, h, w) && t.interrupt().calledBefore(w))))

val aPassOfClosingInterruptsWhatStays = Node.claim(
  "When a pass of closing over the set completes, every thread that was in the set throughout it has been interrupted.")(
  forall((h: Term[ThreadHerd], f: Term[Consumer[Thread]], t: Term[Thread], from: World, to: World) =>
    (ownerClosing(h).pendingAt(from) &&
      exists((answer: Term[Answer[Unit]]) => h.threads.forEach(f).by(h.herdOwner).completed(from, answer, to)) &&
      forall((m: World) => (from.notAfter(m) && m.notAfter(to)) implies elements(h.threads).at(m).contains(t)))
      implies t.interrupt().calledBefore(to)))
```

### `ThreadHerd.scala`, liveness

```scala
val startThreadStartsWhatItAdds = Node.claim("A thread that startThread adds to the set is eventually started.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    h.threads.add(t).called(w) implies w.eventually(later => t.start().calledBefore(later))))

val aStartedForkCallsItsCode = Node.claim(
  "A fork whose thread has been started eventually calls the code it was made to run.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], code: Term[() => Unit], w: World) =>
    (madeToRun(t, h, code, w) && t.start().calledBefore(w)) implies
      w.eventually(later => code().by(t).calledBefore(later))))

val aForkLeavesOnceItsCodeCompletes = Node.claim("Once the code a fork was made to run has completed, the fork leaves.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], code: Term[() => Unit], w: World) =>
    (madeToRun(t, h, code, w) && code().by(t).calledBefore(w) && !code().by(t).pendingAt(w)) implies
      w.eventually(later => left(t, h, later))))

val aForkThatHasLeftFinishes = Node.claim("A fork that has left eventually finishes.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    left(t, h, w) implies w.eventually(later => finished(t, later))))

val closingAsksWhetherTheSetIsEmpty = Node.claim("A call of closing eventually asks whether the set is empty.")(
  forall((h: Term[ThreadHerd], w: World) =>
    ownerClosing(h).called(w) implies w.eventually(later => ownerAsking(h).called(later))))

val closingPassesAndAsksAgain = Node.claim(
  "After closing is answered that the set is not empty, it makes a pass over the set and asks again, provided " +
    "the joins it makes complete.")(
  forall((h: Term[ThreadHerd], a: World, b: World) =>
    (ownerClosing(h).pendingAt(b) && ownerAsking(h).completed(a, Returned(false), b) &&
      forall((t: Term[Thread], j: World) =>
        (b.notAfter(j) && t.join().by(h.herdOwner).called(j)) implies t.join().by(h.herdOwner).settles(j))) implies
      b.eventually(later => b.before(later) && ownerAsking(h).called(later) &&
        exists((f: Term[Consumer[Thread]], p: World, answer: Term[Answer[Unit]], q: World) =>
          b.notAfter(p) && q.notAfter(later) && h.threads.forEach(f).by(h.herdOwner).completed(p, answer, q)))))

val closingCompletesWhenAnsweredEmpty = Node.claim("When closing is answered that the set is empty, it completes.")(
  forall((h: Term[ThreadHerd], a: World, b: World) =>
    (ownerClosing(h).pendingAt(b) && ownerAsking(h).completed(a, Returned(true), b)) implies
      ownerClosing(h).settles(b)))
```

### `unsupervised.scala`

```scala
val closingIsCalledAtTheScopesEnd = Node.claim(
  "Closing a herd is called only by scopedWithCapability of its scope, after the scope's body has completed.")(
  forall((h: Term[ThreadHerd], c: Term[Thread], w: World) =>
    closing(h).by(c).called(w) implies exists([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
      (ox.herd === h) && scopedWithCapability(ox)(f).by(c).pendingAt(w) &&
      f(using ox).by(c).calledBefore(w) && !f(using ox).by(c).pendingAt(w))))

val scopeEndsAfterClosing = Node.claim("A scope run by its owner completes only after closing its herd has completed.")(
  forall([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
    scopedWithCapability(ox)(f).by(ox.herd.herdOwner).everyCall((from, answer, to) => closed(ox.herd, to))))

// Liveness.
val theScopeGoesOnAfterItsBody = Node.claim(
  "Once its body has completed, a scope completes, provided the calls it makes of closing and of runFinalizers do.")(
  forall([T] => (ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
    (scopedWithCapability(ox)(f).by(ox.herd.herdOwner).pendingAt(w) && bodyDone(ox, f, w) &&
      forall((a: World) => ownerClosing(ox.herd).called(a) implies ownerClosing(ox.herd).settles(a)) &&
      forall((r: Term[Either[Throwable, T]], a: World) =>
        runFinalizers(ox, r).called(a) implies runFinalizers(ox, r).settles(a))) implies
      w.eventually(later => done(ox.herd, later))))

// Liveness. `uninterruptible`, which runFinalizers uses, is not modelled.
val runFinalizersCompletes = Node.claim("A call of runFinalizers completes.")(
  forall([T] => (ox: Term[Ox], r: Term[Either[Throwable, T]], w: World) =>
    runFinalizers(ox, r).called(w) implies runFinalizers(ox, r).settles(w)))
```

### `supervised.scala`, `unsupervised.scala`: where Ox runs a scope

```scala
val scopesAreRunOnceByTheirOwner = Node.claim(
  "Ox runs a scope once, in the thread that made its herd.")(
  forall([T] => (ox: Term[Ox], f: Term[Ox ?=> T], c: Term[Thread], w: World) =>
    scopedWithCapability(ox)(f).by(c).called(w) implies ((c === ox.herd.herdOwner) && !opened(ox.herd, w))))
```

### `fork.scala`

```scala
// And the same for forkUnsupervised and forkCancellable.
val onlyForksCallStartThread = Node.claim(
  "startThread of a scope's herd is called only during a call of a fork function with a capability of that scope.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], w: World) =>
    h.startThread(code).by(c).called(w) implies exists([T] => (ox: Term[Ox], user: Term[() => T]) =>
      (ox.herd === h) &&
      (fork(user)(using ox).by(c).pendingAt(w) || forkUser(user)(using ox).by(c).pendingAt(w)))))

val forkReturnsOnlyIfStartThreadDid = Node.claim("A fork function returns only if its call of startThread returned.")(
  forall([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread], k: Term[Fork[T]]) =>
    fork(user)(using ox).by(c).everyCall((from, answer, to) =>
      (answer === Returned(k)) implies
        exists((code: Term[() => Unit]) => ox.herd.startThread(code).by(c).returnedWithin((), from, to)))))

// And the same for fork.
val joinReturnsWhatTheCodeReturned = Node.claim("Joining a fork returns a value only if the fork's code returned it.")(
  forall([T] => (ox: Term[Ox], user: Term[() => T], k: Term[Fork[T]], v: Term[T]) =>
    forkUser(user)(using ox).everyCall((from, answer, to) =>
      (answer === Returned(k)) implies
        k.join().everyCall((a, joined, b) =>
          ((joined === Returned(v)) && to.notAfter(a)) implies
            exists((t: Term[Thread]) => user().by(t).returnedWithin(v, from, b))))))

// Liveness.
val forkCodeCompletesOnceTheUsersDoes = Node.claim(
  "The code a fork function gives startThread completes once the call it makes of the user's code has completed.")(
  forall([T] => (h: Term[ThreadHerd], t: Term[Thread], code: Term[() => Unit], user: Term[() => T], w: World) =>
    (madeToRun(t, h, code, w) && forkFor(t, h, user, w) && code().by(t).pendingAt(w) &&
      forall((a: World) => code().by(t).calls(user(), a) implies user().by(t).settles(a))) implies
      code().by(t).settles(w)))

// Liveness.
val aThrowingForkReports = Node.claim(
  "When the user's code of a fork throws, the fork tells the scope's supervisor of the exception.")(
  forall([T] => (ox: Term[Ox], t: Term[Thread], code: Term[() => Unit], user: Term[() => T]) =>
    forall((e: Term[Throwable], a: World, b: World) =>
      (madeToRun(t, ox.herd, code, a) && forkFor(t, ox.herd, user, a) &&
        code().by(t).calls(user(), a) && user().by(t).completed(a, Threw(e), b)) implies
        b.eventually(later => ox.supervisor.forkException(e).by(t).calledBefore(later)))))
```

### `supervised.scala`, safety

```scala
/** The code does nothing but call the body with the scope: it returns only what that call returned. */
val wraps = define { [T] => (code: Term[() => T], body: Term[Ox ?=> T], ox: Term[Ox]) =>
  forall((t: Term[Thread], a: World, v: Term[T], b: World) =>
    code().by(t).completed(a, Returned(v), b) implies body(using ox).by(t).returnedWithin(v, a, b)) }

val supervisedReturnsItsBodyForksJoin = Node.claim(
  "supervised returns a value only if its supervisor reported success and joining the user fork it made of its " +
    "body returned that value.")(
  forall([T] => (body: Term[Ox ?=> T], o: Term[Thread], v: Term[T]) =>
    supervised(body).by(o).everyCall((from, answer, to) =>
      (answer === Returned(v)) implies
        exists((ox: Term[Ox], f: Term[Ox ?=> T], code: Term[() => T], k: Term[Fork[T]]) =>
          scopedWithCapability(ox)(f).by(o).calledWithin(from, to) && wraps(code, body, ox) &&
          forkUser(code)(using ox).by(o).returnedWithin(k, from, to) &&
          k.join().by(o).returnedWithin(v, from, to) &&
          (outcome(ox.supervisor.result).at(to) === some(Returned(Success)))))))

val successIsReportedAtZero = Node.claim(
  "A supervisor reports success only after a decrement, by the same thread, that left its count at zero.")(
  forall([E] => (s: Term[DefaultSupervisor[E]], c: Term[Thread], w: World) =>
    s.result.complete(Success).by(c).called(w) implies
      exists((a: World, m: World) => m.notAfter(w) && s.running.decrementAndGet().by(c).completed(a, Returned(0), m))))

val countIsPositiveWhileAUserForkHasNotSucceeded = Node.claim(
  "While a user fork of a scope has not reported success, the supervisor's count is positive.")(
  forall((ox: Term[Ox], u: Term[Thread], w: World) =>
    (userFork(u, ox.herd, w) && !ox.supervisor.forkSuccess().by(u).calledBefore(w)) implies
      (count(ox.supervisor.running).at(w) > 0)))
```

### `supervised.scala`, liveness

```scala
val aSupervisorToldOfAnExceptionHasAReport = Node.claim("A supervisor told of an exception eventually has a report.")(
  forall([E] => (s: Term[DefaultSupervisor[E]], e: Term[Throwable], w: World) =>
    s.forkException(e).calledBefore(w) implies w.eventually(later => outcome(s.result).at(later).isDefined)))

val aDecrementToZeroReportsSuccess = Node.claim(
  "A thread whose decrement leaves the supervisor's count at zero goes on to report success.")(
  forall([E] => (s: Term[DefaultSupervisor[E]], c: Term[Thread], a: World, m: World) =>
    s.running.decrementAndGet().by(c).completed(a, Returned(0), m) implies
      m.eventually(later => s.result.complete(Success).by(c).calledBefore(later))))

val countIsZeroOnceAllUserForksSucceeded = Node.claim(
  "When no user fork is being made and every user fork made has reported success, the supervisor's count is zero.")(
  forall((ox: Term[Ox], w: World) =>
    (noUserForkInTheMaking(ox.herd, w) &&
      forall((u: Term[Thread]) => userFork(u, ox.herd, w) implies reportedSuccess(u, ox, w))) implies
      (count(ox.supervisor.running).at(w) === 0)))

val supervisedsBodyOnlyWaitsForTwoJoins = Node.claim(
  "The body supervised gives its scope completes, provided its join of the supervisor and its joins of forks do.")(
  forall([T] => (body: Term[Ox ?=> T], o: Term[Thread], ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
    (supervisedRuns(body, o, ox, f, w) &&
      forall((j: World) => ox.supervisor.join().by(o).called(j) implies ox.supervisor.join().by(o).settles(j)) &&
      forall((k: Term[Fork[T]], j: World) => k.join().by(o).called(j) implies k.join().by(o).settles(j))) implies
      w.eventually(later => bodyDone(ox, f, later))))

val supervisedCompletesOnceItsScopeDoes = Node.claim("supervised completes once the scope it runs has completed.")(
  forall([T] => (body: Term[Ox ?=> T], o: Term[Thread], ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
    (supervisedRuns(body, o, ox, f, w) && done(ox.herd, w)) implies supervised(body).by(o).settles(w)))
```

## 5. Ox: the tree

### Safety: what the local claims add up to

```scala
val liveForksAreInTheSet = Node.claim("A fork that has not left is in its herd's set.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    live(t, h, w) implies elements(h.threads).at(w).contains(t)))

val startThreadCallersStayInside = Node.claim(
  "While a thread is calling startThread of a scope's herd, it is inside the scope.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], w: World) =>
    (h.startThread(code).by(c).called(w) || h.startThread(code).by(c).pendingAt(w)) implies inside(c, h, w)))

val nothingIsAddedOnceEmpty = Node.claim(
  "Once a scope's set is empty after closing was called, no thread is added to it.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], m: World, w: World) =>
    (closing(h).calledBefore(m) && elements(h.threads).at(m).isEmpty && m.notAfter(w)) implies
      !h.threads.add(t).called(w)))

val closedScopeIsEmptyForGood = Node.claim(
  "After closing a scope's herd has completed, every fork of it has left and no thread is added to it.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    closed(h, w) implies
      ((forkOf(t, h, w) implies left(t, h, w)) && !h.threads.add(t).called(w))))

val closedHerdRefusesToStart = Node.claim(
  "After closing a herd has completed, a call of its startThread throws and adds no thread.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], t: Term[Thread]) =>
    h.startThread(code).by(c).everyCall((from, answer, to) =>
      closed(h, from) implies
        ((answer =!= Returned(())) && !h.threads.add(t).by(c).calledWithin(from, to)))))
```

### Safety: the roots

```scala
val noForkRunsAfterItsScope = Node.claim("After a scope has completed, no fork of it runs the code it was made to run.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], code: Term[() => Unit], w: World) =>
    (done(h, w) && madeToRun(t, h, code, w)) implies
      (!code().by(t).pendingAt(w) && !code().by(t).called(w))))

val noForkIsMadeAfterItsScope = Node.claim("After a scope has completed, no fork is made in it.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    done(h, w) implies !h.threads.add(t).called(w)))

val aLateForkIsRefused = Node.claim("A fork attempted after its scope has completed throws and adds no thread.")(
  forall([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread], t: Term[Thread]) =>
    fork(user)(using ox).by(c).everyCall((from, answer, to) =>
      done(ox.herd, from) implies
        (exists((e: Term[Throwable]) => answer === Threw(e)) &&
         !ox.herd.threads.add(t).by(c).calledWithin(from, to)))))

val supervisedReturnsOnlyOnSuccess = Node.claim(
  "supervised returns a value only if its body returned that value and, at some moment after, every user fork " +
    "then made in its scope had succeeded.")(
  forall([T] => (body: Term[Ox ?=> T], o: Term[Thread], v: Term[T]) =>
    supervised(body).by(o).everyCall((from, answer, to) =>
      (answer === Returned(v)) implies
        exists((ox: Term[Ox], f: Term[Ox ?=> T], t: Term[Thread], m: World) =>
          scopedWithCapability(ox)(f).by(o).calledWithin(from, to) && from.notAfter(m) && m.notAfter(to) &&
          body(using ox).by(t).returnedWithin(v, from, m) &&
          forall((u: Term[Thread]) =>
            userFork(u, ox.herd, m) implies ox.supervisor.forkSuccess().by(u).calledBefore(m))))))
```

A call of `supervised` or `unsupervised` runs its scope in the caller's thread. By nesting (rule 3), when that
call completes its scope is done, so A, B and R hold from the moment the public call completes.

### Liveness: what the local claims add up to

```scala
val onlyLiveForksAreInTheSet = Node.claim("Whatever is in a herd's set is a fork that has not left.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    elements(h.threads).at(w).contains(t) implies live(t, h, w)))

val anInterruptedForkLeaves = Node.claim("A fork that has been interrupted eventually leaves.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    (forkOf(t, h, w) && t.interrupt().calledBefore(w)) implies w.eventually(later => left(t, h, later))))

val aJoinInClosingCompletes = Node.claim("A join that closing makes completes.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    (ownerClosing(h).pendingAt(w) && t.join().by(h.herdOwner).called(w)) implies t.join().by(h.herdOwner).settles(w)))

val closingKeepsGoing = Node.claim("A pending closing completes or asks again whether the set is empty.")(
  forall((h: Term[ThreadHerd], w: World) =>
    ownerClosing(h).pendingAt(w) implies
      w.eventually(later => !ownerClosing(h).pendingAt(later) || ownerAsking(h).called(later))))

val everyLiveForkIsInterrupted = Node.claim(
  "While closing is pending, a fork that stays in the set is eventually interrupted.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    (ownerClosing(h).pendingAt(w) && live(t, h, w)) implies
      w.eventually(later => t.interrupt().calledBefore(later) || left(t, h, later))))

val noThreadIsAddedForever = Node.claim("Once a herd's flag is set, there is a moment after which no thread is added.")(
  forall((h: Term[ThreadHerd], w: World) =>
    flag(h.shutdownInProgress).at(w) implies
      w.eventually(last => forall((t: Term[Thread], later: World) =>
        last.notAfter(later) implies !h.threads.add(t).called(later)))))

val theSetEmptiesForGood = Node.claim(
  "While closing is pending, there is a moment from which the herd's set stays empty.")(
  forall((h: Term[ThreadHerd], w: World) =>
    ownerClosing(h).pendingAt(w) implies
      w.eventually(last => !ownerClosing(h).pendingAt(last) ||
        forall((later: World) => last.notAfter(later) implies elements(h.threads).at(later).isEmpty))))

val closingCompletes = Node.claim("A call of closing by the herd's owner completes.")(
  forall((h: Term[ThreadHerd], w: World) => ownerClosing(h).called(w) implies ownerClosing(h).settles(w)))

val theBodyOfASupervisedScopeCompletesOnceReported = Node.claim(
  "Once its supervisor has a report, the body supervised gives its scope completes.")(
  forall([T] => (body: Term[Ox ?=> T], o: Term[Thread], ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
    (supervisedRuns(body, o, ox, f, w) && outcome(ox.supervisor.result).at(w).isDefined) implies
      w.eventually(later => bodyDone(ox, f, later))))
```

### Liveness: the roots

```scala
val aScopeCompletesAfterItsBody = Node.claim("Once the body of a scope has completed, the scope completes.")(
  forall([T] => (ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
    (scopedWithCapability(ox)(f).pendingAt(w) && bodyDone(ox, f, w)) implies
      w.eventually(later => done(ox.herd, later))))

val aFailedForkEndsSupervised = Node.claim(
  "Once the code of a fork of a supervised scope has thrown, supervised completes.")(
  forall([T, U] => (body: Term[Ox ?=> T], o: Term[Thread], ox: Term[Ox], f: Term[Ox ?=> T], user: Term[() => U]) =>
    forall((t: Term[Thread], code: Term[() => Unit], e: Term[Throwable], a: World, b: World) =>
      (supervisedRuns(body, o, ox, f, a) && forkFor(t, ox.herd, user, a) && madeToRun(t, ox.herd, code, a) &&
        code().by(t).calls(user(), a) && user().by(t).completed(a, Threw(e), b)) implies
        supervised(body).by(o).settles(b))))

val supervisedCompletesOnSuccess = Node.claim(
  "Once every user fork made in a supervised scope has reported success, with none being made, supervised completes.")(
  forall([T] => (body: Term[Ox ?=> T], o: Term[Thread], ox: Term[Ox], f: Term[Ox ?=> T], w: World) =>
    (supervisedRuns(body, o, ox, f, w) && exists((u: Term[Thread]) => userFork(u, ox.herd, w)) &&
      noUserForkInTheMaking(ox.herd, w) &&
      forall((u: Term[Thread]) => userFork(u, ox.herd, w) implies reportedSuccess(u, ox, w))) implies
      supervised(body).by(o).settles(w)))
```

By nesting, `unsupervised` completes once the scope it runs has: D is its guarantee.

## 6. The model

```scala
val oxThreads = FrModel("OxThreads")(
  // Safety.
  noForkRunsAfterItsScope, noForkIsMadeAfterItsScope, aLateForkIsRefused, supervisedReturnsOnlyOnSuccess,

  closedScopeIsEmptyForGood.refines(noForkRunsAfterItsScope, noForkIsMadeAfterItsScope),
  scopeEndsAfterClosing.refines(noForkRunsAfterItsScope, noForkIsMadeAfterItsScope, aLateForkIsRefused),
  scopesAreRunOnceByTheirOwner
    .refines(noForkRunsAfterItsScope, noForkIsMadeAfterItsScope, aLateForkIsRefused, aScopeCompletesAfterItsBody),
  codeRunsBeforeLeaving.refines(noForkRunsAfterItsScope, startThreadCallersStayInside)
    .assuming(firstStartSpawnsTheBody, startIsAtomic, newThreadIsUnstarted, currentThreadIsTheCaller),

  closingEndsOnEmpty.refines(closedScopeIsEmptyForGood).assuming(isEmptyIsExact, setCallsAreAtomic,
    joinReturnsOrIsInterrupted, forEachThrowsOnlyWhatItsFunctionDoes, theseJdkCallsReturn),
  liveForksAreInTheSet.refines(closedScopeIsEmptyForGood, nothingIsAddedOnceEmpty, everyLiveForkIsInterrupted)
    .assuming(addPutsItIn, removeTakesOnlyItOut, setCallsAreAtomic),
  nothingIsAddedOnceEmpty.refines(closedScopeIsEmptyForGood),
  startThreadCallersStayInside.refines(nothingIsAddedOnceEmpty).assuming(forksAreMadeFromInside),
  onlyStartThreadAdds.refines(nothingIsAddedOnceEmpty, closedHerdRefusesToStart, noThreadIsAddedForever)
    .assuming(newThreadIsUnstarted),
  onlyForksCallStartThread.refines(startThreadCallersStayInside),
  aForkRemovesOnlyItself.refines(startThreadCallersStayInside).assuming(currentThreadIsTheCaller),
  closingIsCalledAtTheScopesEnd.refines(startThreadCallersStayInside),

  closedHerdRefusesToStart.refines(aLateForkIsRefused),
  closingSetsTheFlag.refines(closedHerdRefusesToStart).assuming(setStores, atomicsAreAtomic),
  theFlagStaysSet.refines(closedHerdRefusesToStart, noThreadIsAddedForever).assuming(setStores),
  startThreadFirstSeesTheFlagUnset.refines(closedHerdRefusesToStart, noThreadIsAddedForever).assuming(getReads),
  forkReturnsOnlyIfStartThreadDid.refines(aLateForkIsRefused),

  supervisedReturnsItsBodyForksJoin.refines(supervisedReturnsOnlyOnSuccess),
  joinReturnsWhatTheCodeReturned.refines(supervisedReturnsOnlyOnSuccess)
    .assuming(firstCompletionStays, completingIsAtomic, getAnswersTheOutcome),
  successIsReportedAtZero
    .refines(supervisedReturnsOnlyOnSuccess, theBodyOfASupervisedScopeCompletesOnceReported)
    .assuming(decrementTakesOne, atomicsAreAtomic),
  countIsPositiveWhileAUserForkHasNotSucceeded
    .refines(supervisedReturnsOnlyOnSuccess, theBodyOfASupervisedScopeCompletesOnceReported)
    .assuming(incrementAddsOne, atomicsAreAtomic),

  // Liveness.
  aFailedForkEndsSupervised, supervisedCompletesOnSuccess,
  aScopeCompletesAfterItsBody.refines(aFailedForkEndsSupervised, supervisedCompletesOnSuccess),

  closingCompletes.refines(aScopeCompletesAfterItsBody),
  theScopeGoesOnAfterItsBody.refines(aScopeCompletesAfterItsBody),
  runFinalizersCompletes.refines(aScopeCompletesAfterItsBody).assuming(finalizersComplete),

  theSetEmptiesForGood.refines(closingCompletes),
  closingKeepsGoing.refines(closingCompletes, everyLiveForkIsInterrupted),
  closingCompletesWhenAnsweredEmpty.refines(closingCompletes, closingKeepsGoing).assuming(isEmptyIsExact),

  everyLiveForkIsInterrupted.refines(theSetEmptiesForGood),
  anInterruptedForkLeaves.refines(theSetEmptiesForGood, aJoinInClosingCompletes),
  noThreadIsAddedForever.refines(theSetEmptiesForGood),
  onlyLiveForksAreInTheSet.refines(theSetEmptiesForGood).assuming(addPutsItIn, removeTakesOnlyItOut, setCallsAreAtomic),

  closingPassesAndAsksAgain.refines(everyLiveForkIsInterrupted, closingKeepsGoing)
    .assuming(forEachCompletes, interruptIsAtomic),
  aPassOfClosingInterruptsWhatStays.refines(everyLiveForkIsInterrupted).assuming(forEachReachesWhatStays),
  closingAsksWhetherTheSetIsEmpty.refines(closingKeepsGoing),
  aJoinInClosingCompletes.refines(closingKeepsGoing),
  closingJoinsOnlyInterruptedForks.refines(aJoinInClosingCompletes).assuming(forEachGivesOnlyElements),
  aForkThatHasLeftFinishes.refines(aJoinInClosingCompletes).assuming(joinCompletesOnceFinished),

  startThreadStartsWhatItAdds.refines(anInterruptedForkLeaves).assuming(startIsAtomic),
  aStartedForkCallsItsCode.refines(anInterruptedForkLeaves).assuming(firstStartSpawnsTheBody, aStartedThreadRuns),
  forkCodeCompletesOnceTheUsersDoes.refines(anInterruptedForkLeaves).assuming(forkCodeStopsWhenInterrupted),
  aForkLeavesOnceItsCodeCompletes.refines(anInterruptedForkLeaves),

  aThrowingForkReports.refines(aFailedForkEndsSupervised),
  aSupervisorToldOfAnExceptionHasAReport.refines(aFailedForkEndsSupervised)
    .assuming(firstCompletionStays, completingIsAtomic),
  theBodyOfASupervisedScopeCompletesOnceReported.refines(aFailedForkEndsSupervised, supervisedCompletesOnSuccess),
  supervisedsBodyOnlyWaitsForTwoJoins.refines(theBodyOfASupervisedScopeCompletesOnceReported)
    .assuming(getCompletesOnceThereIsAnOutcome),
  supervisedCompletesOnceItsScopeDoes.refines(aFailedForkEndsSupervised, supervisedCompletesOnSuccess)
    .assuming(forEachCompletes),
  countIsZeroOnceAllUserForksSucceeded.refines(supervisedCompletesOnSuccess).assuming(incrementAddsOne, decrementTakesOne),
  aDecrementToZeroReportsSuccess.refines(supervisedCompletesOnSuccess).assuming(firstCompletionStays, completingIsAtomic))
```

## 7. Left out, and open

Safety:

- **`isEmptyIsExact` is more than the JDK promises.** If it is false, A and B are false of Ox as written.
- **`forksAreMadeFromInside` leaves out one legal use:** a fork of an inner scope forking into an outer scope.
  Covering it needs `inside` to be recursive, which FrFlow does not have.
- **C's tree is likely one node short:** that the fork of the body is the first user fork of its scope.

Liveness:

- **Progress (rule 6) is an assumption about the scheduler with no formula.** The vocabulary speaks of calls, not
  of single steps of code, so "a thread running code takes its next step" cannot be a node as things stand.
- **D sits under E and F, so in FrFlow's sense it is not a root,** although it is the guarantee for `unsupervised`.
  Either a root may also be a part, or E and F take D's parts directly.
- **`theBodyOfASupervisedScopeCompletesOnceReported` is one local claim short:** that a user fork which reports
  success has completed its own future first, so joining the body's fork does not wait.
- **`noThreadIsAddedForever` rests on rule 7** (finitely many threads at a moment), not on a node.
- **Nothing is claimed about a fork that ignores interruption,** nor about `forkUnsupervised` and `forkCancellable`.

Both:

- **Steps are not built.** The section on steps says what the generated meaning must contain; FrFlow has no such
  meaning for threaded code yet. Without it "every run" and "atomic" mean nothing.
- **No claim says Ox is free of data races.** The model gives every field one value at each moment, which the JVM
  promises only to programs without a data race. The hand-written machine proved race freedom; here it is taken
  for granted. It should come back as a claim FrFlow states of every threaded model, since it needs no words from
  the developer.
- **Not modelled:** resources beyond "finalizers complete", application errors (`supervisedError` with an error
  mode), fork locals, what a scope throws, `uninterruptible`, exceptions the JDK itself may throw.
- **Words used beyond the six primitives agreed so far:** `outer.calls(inner, w)` as a seventh primitive; the
  defined `notAfter`, `calledWithin`, `returnedWithin`, `eventually`, `settles`; a type quantified in `forall` and
  in `define`; and rules 3 and 5 to 7.
