package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import ox.internal.ThreadHerd
import ox.threads.*

// What a fork does in time: `startThread` starts the thread it added; the thread runs the function it was made
// for, which runs the code, takes the thread out of the herd's set, and ends.

val startThreadAddsOnce = Node.claim("A call of startThread itself makes at most one call that adds to a set.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], from: Term[BigInt]) =>
    forall((s: Obj[ConcurrentSet], t: Obj[Thread], a: Term[BigInt]) =>
      forall((s2: Obj[ConcurrentSet], t2: Obj[Thread], a2: Term[BigInt]) =>
        (starting(h, code).by(c).called(from) && s.add(t).by(c).calledInside(from, a) &&
          s2.add(t2).by(c).calledInside(from, a2)) implies (a === a2)))))

val startThreadStartsWhatItAdded = Node.claim(
  "A call of startThread that has itself added a thread to the herd's set calls start on that thread, in time.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], a: Term[BigInt], added: Term[Value], b: Term[BigInt]) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, a) &&
        threads(h).add(t).by(c).completed(a, make[Response.Returned](added), b)) implies
        exists((m: Term[BigInt]) => t.start().by(c).calledInside(from, m)))))

val startThreadStartsAfterItsAddIsOver = Node.claim(
  "A call of startThread itself starts a thread only once each call it itself made to add to the herd's set is " +
    "over.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], w: Term[BigInt], m: Term[BigInt], started: Obj[Thread]) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, w) &&
        started.start().by(c).calledInside(from, m)) implies !threads(h).add(t).by(c).pendingSince(w, m))))

val aForkFunctionRemovesItsThread = Node.claim(
  "A call of a function startThread handed a thread factory that has completed has asked for the current " +
    "thread and then removed it from the herd's set, by a call that is over.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], code: Obj[Code], t: Obj[Thread]) =>
    forall((i: Term[BigInt], ended: Term[Response], e: Term[BigInt]) =>
      (forkFunction(r, h, code) && running(r).by(t).completed(i, ended, e)) implies
        exists((a: Term[BigInt], b: Term[BigInt]) =>
          Thread.currentThread().by(t).completed(a, Returned(t), b) &&
            threads(h).remove(t).by(t).completedWithin(b, e)))))

val aForkFunctionCompletesOnceItsCodeDoes = Node.claim(
  "A call of a function startThread handed a thread factory is responded to in time, if each call it itself " +
    "makes of the code startThread was given is.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], code: Obj[Code], t: Obj[Thread], i: Term[BigInt]) =>
    (forkFunction(r, h, code) && running(r).by(t).called(i) &&
      forall((m: Term[BigInt]) => code().by(t).calledInside(i, m) implies code().by(t).respondedTo(m))) implies
      running(r).by(t).respondedTo(i)))

val aForkEndsOnceInterrupted = Node.claim(
  "A thread added to a herd's set runs, to its end and in time, the function a factory made it for, once it " +
    "has been interrupted.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], code: Obj[Code], made: Term[BigInt]) =>
    (madeToRun(t, h, code, made) && interrupted(t)) implies
      exists((f: Obj[ThreadFactory], r: Obj[Runnable], a: Term[BigInt], b: Term[BigInt], i: Term[BigInt]) =>
        f.newThread(r).completed(a, Returned(t), b) && running(r).by(t).respondedTo(i))))
