package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import ox.internal.ThreadHerd
import ox.threads.*

// That a fork leaves for good: the function it runs takes its thread out of the herd's set, and nothing puts it
// back.

// The JDK's `ConcurrentHashMap`: a key is in the map from the insertion a call of `add` makes to the removal a
// call of `remove` makes, each done once, in the bin's lock.
val anElementEntersOnlyWhenAdded = Node.assumption(
  "An element enters a plain concurrent set only at a moment during a call that adds it.")(
  forall((s: Obj[ConcurrentSet], x: Obj[AnyRef], w: Term[BigInt]) =>
    (plainSet(s) && !elements(s, w).contains(x.asValue) && elements(s, w + 1).contains(x.asValue)) implies
      s.add(x).inProgress(w)))

// Of an object: `remove(null)` throws, and takes nothing out.
val removingTakesTheElementOut = Node.assumption(
  "A call that removes an object from a concurrent set takes it out at one moment during the call, and nothing " +
    "else.")(
  forall((s: Obj[ConcurrentSet], x: Obj[AnyRef]) =>
    (x.asValue =!= noObject) implies s.remove(x).everyCall((from, _, to) =>
      exists((m: Term[BigInt]) => from <= m && m < to && forall((y: Term[Value]) =>
        elements(s, m + 1).contains(y) === ((y =!= x.asValue) && elements(s, m).contains(y)))))))

// The JVM: a thread begins to run when `start` is called on it (`Thread.start`), and not before.
val aThreadActsOnlyOnceStarted = Node.assumption(
  "A thread a factory made makes no call before start is called on it.")(
  forall((f: Obj[ThreadFactory], r: Obj[Runnable], t: Obj[Thread]) =>
    forall((a: Term[BigInt], b: Term[BigInt], made: Term[Invocation], w: Term[BigInt]) =>
      (f.newThread(r).completed(a, Returned(t), b) && calledBy(made, t.asValue, w)) implies
        t.start().calledBefore(w))))

val currentThreadIsAnObject = Node.assumption("`Thread.currentThread()` gives no null.")(
  Thread.currentThread().everyCall((_, a, _) => a =!= make[Response.Returned](noObject)))

val aForkThatEndedStaysOut = Node.claim(
  "Once a function startThread handed a thread factory has completed on a thread, the thread is out of the " +
    "herd's set for good.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], code: Obj[Code], t: Obj[Thread]) =>
    forall((i: Term[BigInt], ended: Term[Response], e: Term[BigInt], w: Term[BigInt], b: Term[BigInt]) =>
      (h.isConstructed(b) && forkFunction(r, h, code) && running(r).by(t).completed(i, ended, e) && e <= w) implies
        !elements(threads(h), w).contains(t.asValue))))

val anInterruptedForkLeavesForGood = Node.claim(
  "A thread added to a herd's set is out of it for good from some moment on, once it has been interrupted.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], code: Obj[Code], made: Term[BigInt]) =>
    (madeToRun(t, h, code, made) && interrupted(t)) implies
      exists((e: Term[BigInt]) =>
        forall((w: Term[BigInt]) => (e <= w) implies !elements(threads(h), w).contains(t.asValue)))))
