# Ox threads: the model, as a sketch

Status: a sketch to iterate on. Nothing here is compiled or run; the words in section 0 are not built.
The Scala is Ox's own code, unchanged (`ThreadHerd.scala`, `unsupervised.scala`, `fork.scala`, `supervised.scala`).

## The tree

```
A  noForkRunsAfterItsScope            After a scope has completed, no fork of it runs its code.
├─ closedScopeIsEmptyForGood          After closing has completed, every fork has left and no thread is added.
│  ├─ closingEndsOnEmpty              local   ThreadHerd            <- isEmptyIsExact
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
└─ countIsPositiveUntilSuccess        local   supervised.scala      <- incrementAddsOne   (formula open)
```

What the sketch shows:

- **A and B rest on three things:** the herd's set, an exact `isEmpty`, and callers staying inside the scope.
  `join`, `interrupt` and `forEach` are not needed for them: they only matter for the scope completing at all.
- **The flag gives a separate guarantee (R)** that needs no assumption about callers.
- **"A fork has finished" cannot mean "its thread has finished".** Closing leaves when the set is empty, and a
  thread takes itself out of the set a few steps before it ends. The claim is about the fork's code.
- **A scope is identified by its herd.** Ox makes copies of a capability (`asNoErrorMode`); all share the herd.

## 0. Words used (FrFlow, to be built)

A run is a sequence of moments. Between two consecutive moments one actor (a thread) takes one step.

| Primitive | Meaning |
|---|---|
| `World`, `a.before(b)` | A moment of a run; `a` is earlier than `b` in the same run. |
| `x.at(w)` | The value of something that changes, at a moment. |
| `call.by(who)` | The actor that makes the call; omitted means any. |
| `call.called(w)` | The call is made at `w`. |
| `call.completed(from, answer, to)` | The call made at `from` completes at `to` with `answer`. |
| `call.spawned(w)` | At `w` the call is given to its actor to run concurrently. |

| Defined from them | Meaning |
|---|---|
| `call.everyCall((from, answer, to) => p)` | `p` for every completed call. |
| `call.atomic` | Every call completes at the very next moment. |
| `call.wasCalled.at(w)` | A call was made before `w`. |
| `call.pending.at(w)` | A call was made before `w` and has not completed by `w`. |
| `call.calledWithin(from, to)` | A call was made at a moment from `from` to `to`. |
| `call.returnedWithin(v, from, to)` | A call made and completed from `from` to `to` returned `v`. |
| `a.notAfter(b)` | `a` is `b` or earlier. |
| `changing(w => …)` | Builds something that changes from a formula over the moment. |

`answer` is `Returned(v)` or `Threw(e)`.

Spelling: a member of real code is written on the object (`h.threads`, `s.add(x)`); a word of the model is applied
to it (`elements(s)`, `live(t, h)`); FrFlow's words are on a call or a moment.

Rules of the model (not nodes):

1. **Frame.** A step changes only the words its assumption or its code names.
2. **Spawning.** A call that no code calls begins only after it was spawned, once.
3. **Nesting.** A call an actor makes during another of its calls completes first.
4. **Closed JDK.** A JDK method calls only what its assumptions say.

## 1. The JVM: assumptions on its methods

```scala
type KeySet[A] = ConcurrentHashMap.KeySetView[A, java.lang.Boolean]

// Words of the model for JDK types. They are not JDK members.
def elements[A] = Declaration[KeySet[A] => Changing[Set[A]]]("what is in the set")
val flag        = Declaration[AtomicBoolean => Changing[Boolean]]("what the atomic boolean holds")
val count       = Declaration[AtomicInteger => Changing[Int]]("what the atomic integer holds")
def outcome[A]  = Declaration[CompletableFuture[A] => Changing[Option[Answer[A]]]]("what the future was completed with")
val body        = Declaration[Thread => Runnable]("the code the thread was made to run")
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
```

### Threads

```scala
val startIsAtomic = Node.assumption("Starting a thread is atomic.")(
  forall((t: Term[Thread]) => t.start().atomic))

val firstStartSpawnsTheBody = Node.assumption("Starting a thread for the first time gives the thread its body to run.")(
  forall((t: Term[Thread]) =>
    t.start().everyCall((from, answer, to) =>
      !t.start().wasCalled.at(from) implies body(t).run().by(t).spawned(to))))

val currentThreadIsTheCaller = Node.assumption("Asking for the current thread answers the thread that asks.")(
  forall((t: Term[Thread]) =>
    Thread.currentThread().by(t).everyCall((from, answer, to) => answer === Returned(t))))

// Ox's factory can be replaced by the user: this is assumed of whichever is used.
val newThreadIsUnstarted = Node.assumption(
  "A thread factory answers a thread that has not been started, whose body is the code it was given.")(
  forall((factory: Term[ThreadFactory], r: Term[Runnable], t: Term[Thread]) =>
    factory.newThread(r).everyCall((from, answer, to) =>
      (answer === Returned(t)) implies ((body(t) === r) && !t.start().wasCalled.at(to)))))
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
```

## 2. Ox: the words of the model

A scope is named by its herd `h`. Every word is defined from calls of Ox's own code.

```scala
def closing(h: Term[ThreadHerd]) = h.interruptAllAndJoinUntilCompleted()   // an abbreviation, plain Scala

/** The thread is a fork of the scope: the herd has added it to its set. */
val forkOf = define { (t: Term[Thread], h: Term[ThreadHerd]) => changing(w => h.threads.add(t).wasCalled.at(w)) }

/** The fork has left: it has taken itself out of the set. */
val left = define { (t: Term[Thread], h: Term[ThreadHerd]) => changing(w => h.threads.remove(t).wasCalled.at(w)) }

/** The fork has not left. */
val live = define { (t: Term[Thread], h: Term[ThreadHerd]) => changing(w => forkOf(t, h).at(w) && !left(t, h).at(w)) }

/** The fork was made to run this code: its thread was added during `startThread(code)`, by its caller. */
val madeToRun = define { (t: Term[Thread], h: Term[ThreadHerd], code: Term[() => Unit]) =>
  changing(w => exists((c: Term[Thread], m: World) =>
    m.before(w) && h.threads.add(t).by(c).called(m) && h.startThread(code).by(c).pending.at(m))) }

/** Closing the herd, by its owner, has completed. */
val closed = define { (h: Term[ThreadHerd]) =>
  changing(w => closing(h).by(h.herdOwner).wasCalled.at(w) && !closing(h).by(h.herdOwner).pending.at(w)) }

/** The scope has been opened: `scopedWithCapability` was called with a capability of this herd. */
val opened = define { (h: Term[ThreadHerd]) => changing(w => exists([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
  (ox.herd === h) && scopedWithCapability(ox)(f).wasCalled.at(w))) }

/** The scope is running. */
val running = define { (h: Term[ThreadHerd]) => changing(w => exists([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
  (ox.herd === h) && scopedWithCapability(ox)(f).pending.at(w))) }

/** The scope has completed. */
val done = define { (h: Term[ThreadHerd]) => changing(w => opened(h).at(w) && !running(h).at(w)) }

/** The thread is inside the scope: its owner before closing is called, or a fork of it that has not left. */
val inside = define { (c: Term[Thread], h: Term[ThreadHerd]) => changing(w =>
  ((c === h.herdOwner) && running(h).at(w) && !closing(h).wasCalled.at(w)) || live(c, h).at(w)) }

/** The thread is a user fork of the scope: it was added during a call of `forkUser` with the scope's capability. */
val userFork = define { (u: Term[Thread], h: Term[ThreadHerd]) =>
  changing(w => exists([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread], m: World) =>
    (ox.herd === h) && m.before(w) && h.threads.add(u).by(c).called(m) && forkUser(user)(using ox).by(c).pending.at(m))) }
```

`fork` and `forkUser` stand for `forkError` and `forkUserError`, which they call.

## 3. Ox: what is assumed of its callers

```scala
// With capture checking this would be what the compiler says, not an assumption.
val forksAreMadeFromInside = Node.assumption(
  "A fork is made in a scope only by a thread inside it: its owner before closing, or a fork of it that has not left.")(
  forall([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread], w: World) =>
    (fork(user)(using ox).by(c).called(w) || forkUser(user)(using ox).by(c).called(w)) implies
      inside(c, ox.herd).at(w)))
```

## 4. Ox: local claims, each provable from one piece of code and the JVM assumptions

### `ThreadHerd.scala`

```scala
val onlyStartThreadAdds = Node.claim(
  "A thread is added to a herd's set only during a call of startThread, by its caller, and has not been started.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], c: Term[Thread], w: World) =>
    h.threads.add(t).by(c).called(w) implies
      (exists((code: Term[() => Unit]) => h.startThread(code).by(c).pending.at(w)) && !t.start().wasCalled.at(w))))

val aForkRemovesOnlyItself = Node.claim("A thread is removed from a herd's set only by itself.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], c: Term[Thread], w: World) =>
    h.threads.remove(t).by(c).called(w) implies (c === t)))

val codeRunsBeforeLeaving = Node.claim(
  "A fork calls the code it was made to run only before it leaves, and leaves only when no such call is pending.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], code: Term[() => Unit], w: World) =>
    madeToRun(t, h, code).at(w) implies
      ((code().by(t).called(w) implies !left(t, h).at(w)) &&
       (h.threads.remove(t).called(w) implies !code().by(t).pending.at(w)))))

val closingEndsOnEmpty = Node.claim(
  "Closing a herd completes only after a moment, during it, at which the herd's set is empty.")(
  forall((h: Term[ThreadHerd]) =>
    closing(h).by(h.herdOwner).everyCall((from, answer, to) =>
      exists((m: World) => from.before(m) && m.notAfter(to) && elements(h.threads).at(m).isEmpty))))

val closingSetsTheFlag = Node.claim("When closing a herd completes, the herd's flag is set.")(
  forall((h: Term[ThreadHerd]) =>
    closing(h).by(h.herdOwner).everyCall((from, answer, to) => flag(h.shutdownInProgress).at(to))))

val theFlagStaysSet = Node.claim("Once a herd's flag is set, it stays set.")(
  forall((h: Term[ThreadHerd], a: World, b: World) =>
    (a.before(b) && flag(h.shutdownInProgress).at(a)) implies flag(h.shutdownInProgress).at(b)))

val startThreadFirstSeesTheFlagUnset = Node.claim(
  "startThread adds a thread, or returns, only after it has seen the herd's flag unset.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], t: Term[Thread], from: World, w: World) =>
    (h.startThread(code).by(c).called(from) && from.before(w) &&
      (h.threads.add(t).by(c).called(w) || h.startThread(code).by(c).completed(from, Returned(()), w))) implies
      exists((m: World) => from.notAfter(m) && m.before(w) && !flag(h.shutdownInProgress).at(m))))
```

### `unsupervised.scala`

```scala
val closingIsCalledAtTheScopesEnd = Node.claim(
  "Closing a herd is called only by scopedWithCapability of its scope, after the scope's body has completed.")(
  forall((h: Term[ThreadHerd], c: Term[Thread], w: World) =>
    closing(h).by(c).called(w) implies exists([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
      (ox.herd === h) && scopedWithCapability(ox)(f).by(c).pending.at(w) &&
      f(using ox).by(c).wasCalled.at(w) && !f(using ox).by(c).pending.at(w))))

val scopeEndsAfterClosing = Node.claim("A scope run by its owner completes only after closing its herd has completed.")(
  forall([T] => (ox: Term[Ox], f: Term[Ox ?=> T]) =>
    scopedWithCapability(ox)(f).by(ox.herd.herdOwner).everyCall((from, answer, to) => closed(ox.herd).at(to))))
```

### `supervised.scala`, `unsupervised.scala`: where Ox runs a scope

```scala
val scopesAreRunOnceByTheirOwner = Node.claim(
  "Ox runs a scope once, in the thread that made its herd.")(
  forall([T] => (ox: Term[Ox], f: Term[Ox ?=> T], c: Term[Thread], w: World) =>
    scopedWithCapability(ox)(f).by(c).called(w) implies ((c === ox.herd.herdOwner) && !opened(ox.herd).at(w))))
```

### `fork.scala`

```scala
// And the same for forkUnsupervised and forkCancellable.
val onlyForksCallStartThread = Node.claim(
  "startThread of a scope's herd is called only during a call of a fork function with a capability of that scope.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], w: World) =>
    h.startThread(code).by(c).called(w) implies exists([T] => (ox: Term[Ox], user: Term[() => T]) =>
      (ox.herd === h) &&
      (fork(user)(using ox).by(c).pending.at(w) || forkUser(user)(using ox).by(c).pending.at(w)))))

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
```

### `supervised.scala`

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

// Open. It has to name "the fork this call makes" from its announcement (forkStarts), before the fork's thread
// exists. `wasCalled` is a Boolean and cannot count calls; a count of calls may be the missing word.
val countIsPositiveUntilSuccess = Node.claim(
  "From the moment a user fork is announced until it reports success, the supervisor's count is positive.")(???)
```

## 5. Ox: the tree

### What the local claims add up to

```scala
val liveForksAreInTheSet = Node.claim("A fork that has not left is in its herd's set.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    live(t, h).at(w) implies elements(h.threads).at(w).contains(t)))

val startThreadCallersStayInside = Node.claim(
  "While a thread is calling startThread of a scope's herd, it is inside the scope.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], w: World) =>
    (h.startThread(code).by(c).called(w) || h.startThread(code).by(c).pending.at(w)) implies inside(c, h).at(w)))

val nothingIsAddedOnceEmpty = Node.claim(
  "Once a scope's set is empty after closing was called, no thread is added to it.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], m: World, w: World) =>
    (closing(h).wasCalled.at(m) && elements(h.threads).at(m).isEmpty && m.notAfter(w)) implies
      !h.threads.add(t).called(w)))

val closedScopeIsEmptyForGood = Node.claim(
  "After closing a scope's herd has completed, every fork of it has left and no thread is added to it.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    closed(h).at(w) implies
      ((forkOf(t, h).at(w) implies left(t, h).at(w)) && !h.threads.add(t).called(w))))

val closedHerdRefusesToStart = Node.claim(
  "After closing a herd has completed, a call of its startThread throws and adds no thread.")(
  forall((h: Term[ThreadHerd], code: Term[() => Unit], c: Term[Thread], t: Term[Thread]) =>
    h.startThread(code).by(c).everyCall((from, answer, to) =>
      closed(h).at(from) implies
        ((answer =!= Returned(())) && !h.threads.add(t).by(c).calledWithin(from, to)))))
```

### The roots

```scala
val noForkRunsAfterItsScope = Node.claim("After a scope has completed, no fork of it runs the code it was made to run.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], code: Term[() => Unit], w: World) =>
    (done(h).at(w) && madeToRun(t, h, code).at(w)) implies
      (!code().by(t).pending.at(w) && !code().by(t).called(w))))

val noForkIsMadeAfterItsScope = Node.claim("After a scope has completed, no fork is made in it.")(
  forall((h: Term[ThreadHerd], t: Term[Thread], w: World) =>
    done(h).at(w) implies !h.threads.add(t).called(w)))

val aLateForkIsRefused = Node.claim("A fork attempted after its scope has completed throws and adds no thread.")(
  forall([T] => (ox: Term[Ox], user: Term[() => T], c: Term[Thread], t: Term[Thread]) =>
    fork(user)(using ox).by(c).everyCall((from, answer, to) =>
      done(ox.herd).at(from) implies
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
            userFork(u, ox.herd).at(m) implies ox.supervisor.forkSuccess().by(u).wasCalled.at(m))))))
```

A call of `supervised` or `unsupervised` runs its scope in the caller's thread. By nesting (rule 3), when that
call completes its scope is done, so A, B and R hold from the moment the public call completes.

## 6. The model

```scala
val oxThreads = FrModel("OxThreads")(
  noForkRunsAfterItsScope, noForkIsMadeAfterItsScope, aLateForkIsRefused, supervisedReturnsOnlyOnSuccess,

  closedScopeIsEmptyForGood.refines(noForkRunsAfterItsScope, noForkIsMadeAfterItsScope),
  scopeEndsAfterClosing.refines(noForkRunsAfterItsScope, noForkIsMadeAfterItsScope, aLateForkIsRefused),
  scopesAreRunOnceByTheirOwner.refines(noForkRunsAfterItsScope, noForkIsMadeAfterItsScope, aLateForkIsRefused),
  codeRunsBeforeLeaving.refines(noForkRunsAfterItsScope, startThreadCallersStayInside)
    .assuming(firstStartSpawnsTheBody, startIsAtomic, newThreadIsUnstarted, currentThreadIsTheCaller),

  closingEndsOnEmpty.refines(closedScopeIsEmptyForGood).assuming(isEmptyIsExact, setCallsAreAtomic),
  liveForksAreInTheSet.refines(closedScopeIsEmptyForGood, nothingIsAddedOnceEmpty)
    .assuming(addPutsItIn, removeTakesOnlyItOut, setCallsAreAtomic),
  nothingIsAddedOnceEmpty.refines(closedScopeIsEmptyForGood),
  startThreadCallersStayInside.refines(nothingIsAddedOnceEmpty).assuming(forksAreMadeFromInside),
  onlyStartThreadAdds.refines(nothingIsAddedOnceEmpty, closedHerdRefusesToStart).assuming(newThreadIsUnstarted),
  onlyForksCallStartThread.refines(startThreadCallersStayInside),
  aForkRemovesOnlyItself.refines(startThreadCallersStayInside).assuming(currentThreadIsTheCaller),
  closingIsCalledAtTheScopesEnd.refines(startThreadCallersStayInside),

  closedHerdRefusesToStart.refines(aLateForkIsRefused),
  closingSetsTheFlag.refines(closedHerdRefusesToStart).assuming(setStores, atomicsAreAtomic),
  theFlagStaysSet.refines(closedHerdRefusesToStart).assuming(setStores),
  startThreadFirstSeesTheFlagUnset.refines(closedHerdRefusesToStart).assuming(getReads),
  forkReturnsOnlyIfStartThreadDid.refines(aLateForkIsRefused),

  supervisedReturnsItsBodyForksJoin.refines(supervisedReturnsOnlyOnSuccess),
  joinReturnsWhatTheCodeReturned.refines(supervisedReturnsOnlyOnSuccess)
    .assuming(firstCompletionStays, completingIsAtomic, getAnswersTheOutcome),
  successIsReportedAtZero.refines(supervisedReturnsOnlyOnSuccess).assuming(decrementTakesOne, atomicsAreAtomic),
  countIsPositiveUntilSuccess.refines(supervisedReturnsOnlyOnSuccess).assuming(incrementAddsOne, atomicsAreAtomic))
```

## 7. Left out, and open

- **The roots are "only if" and "never".** A scope that never completes meets all four. The other half (a scope
  does complete once its forks do; a body is run) needs liveness.
- **`isEmptyIsExact` is more than the JDK promises.** If it is false, A and B are false of Ox as written.
- **`forksAreMadeFromInside` leaves out one legal use:** a fork of an inner scope forking into an outer scope.
  Covering it needs `inside` to be recursive, which FrFlow does not have.
- **`countIsPositiveUntilSuccess` has no formula** (see the comment on it).
- **Not modelled:** finalizers and resources, application errors (`supervisedError` with an error mode),
  `forkUnsupervised`, `forkCancellable`, fork locals, what a scope throws, exceptions the JDK itself may throw.
- **Words used here beyond the six primitives:** `changing`, `notAfter`, `calledWithin`, `returnedWithin`, a type
  quantified in `forall` and in `define`, and the nesting rule.
