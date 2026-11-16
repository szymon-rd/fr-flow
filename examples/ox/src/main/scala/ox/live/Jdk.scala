package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import java.util.concurrent.atomic.AtomicBoolean
import java.util.function.Consumer
import ox.threads.*

// What is assumed of the JDK, in time: its calls are responded to, some on a condition.

val interruptResponds = Node.assumption("A call of interrupt on a thread is responded to, in time.")(
  forall((t: Obj[Thread]) => t.interrupt().responds))

val addSuppressedResponds = Node.assumption("A call of addSuppressed on an exception is responded to, in time.")(
  forall((x: Obj[Throwable], y: Obj[Throwable]) => x.addSuppressed(y).responds))

// Of the JDK and of the thread factory: the thread it makes for a function ends when the function does.
val joinRespondsOnceItsThreadHasRun = Node.assumption(
  "A call of join on a thread a factory made for a function is responded to in time, once the thread's call " +
    "of the function has been.")(
  forall((f: Obj[ThreadFactory], r: Obj[Runnable], t: Obj[Thread], c: Obj[Thread]) =>
    forall((a: Term[BigInt], b: Term[BigInt], i: Term[BigInt], from: Term[BigInt]) =>
      (f.newThread(r).completed(a, Returned(t), b) && running(r).by(t).respondedTo(i) &&
        t.join().by(c).called(from)) implies t.join().by(c).respondedTo(from))))

// A traversal of a concurrent set goes through what the set holds while it runs: it ends when no more is added.
val aTraversalRespondsOnceItsFunctionDoes = Node.assumption(
  "A traversal of a concurrent set to which nothing more is added is responded to in time, if each call of its " +
    "function that it itself makes is.")(
  forall((s: Obj[ConcurrentSet], f: Obj[Consumer[AnyRef]], c: Obj[Thread], from: Term[BigInt]) =>
    (s.forEach(f).by(c).called(from) && addingStops(s) &&
      forall((x: Obj[AnyRef], m: Term[BigInt]) =>
        f.accept(x).by(c).calledInside(from, m) implies f.accept(x).by(c).respondedTo(m))) implies
      s.forEach(f).by(c).respondedTo(from)))

val aTraversalAppliesItsFunctionToElements = Node.assumption(
  "A traversal of a concurrent set applies its function only to what is in the set at a moment from its call " +
    "to the application.")(
  forall((s: Obj[ConcurrentSet], f: Obj[Consumer[AnyRef]], c: Obj[Thread], x: Obj[AnyRef]) =>
    forall((from: Term[BigInt], m: Term[BigInt]) =>
      (s.forEach(f).by(c).called(from) && f.accept(x).by(c).calledInside(from, m)) implies
        exists((w: Term[BigInt]) => from <= w && w <= m && elements(s, w).contains(x.asValue)))))

// What is in a set got there by `add`, and the call that put it there returns: it may still be pending.
val anElementWasAdded = Node.assumption(
  "What is in a plain concurrent set is there by a call that adds it, and returns.")(
  forall((s: Obj[ConcurrentSet], x: Obj[AnyRef], w: Term[BigInt]) =>
    (plainSet(s) && elements(s, w).contains(x.asValue)) implies
      exists((c: Obj[Thread], from: Term[BigInt], added: Term[Value], to: Term[BigInt]) =>
        s.add(x).by(c).completed(from, make[Response.Returned](added), to))))

val settingResponds = Node.assumption("A call that sets an atomic boolean is responded to, in time.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) => s.set(b).responds))

val addingResponds = Node.assumption("A call that adds to a concurrent set is responded to, in time.")(
  forall((s: Obj[ConcurrentSet], x: Obj[AnyRef]) => s.add(x).responds))

val isEmptyResponds = Node.assumption(
  "A call that asks a concurrent set whether it is empty is responded to, in time.")(
  forall((s: Obj[ConcurrentSet]) => s.isEmpty().responds))

// `isEmpty` sums counters: with nothing in the set and every call that removed from it over, each decrement has
// been counted, so the sum is not above what the set holds.
val isEmptyFindsARestingSetEmpty = Node.assumption(
  "A concurrent set that holds nothing from a moment on, with no call that removes from it in progress, answers " +
    "that it is empty to a call made from that moment on.")(
  forall((s: Obj[ConcurrentSet], rest: Term[BigInt]) =>
    forall((y: Obj[AnyRef], w: Term[BigInt]) =>
      (rest <= w) implies (!elements(s, w).contains(y.asValue) && !s.remove(y).inProgress(w))) implies
      s.isEmpty().everyCall((from, a, _) => (rest <= from) implies (a === Returned(True)))))
