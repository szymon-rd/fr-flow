package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import ox.internal.ThreadHerd
import ox.threads.*

// What is assumed to happen in time. Of code: a thread running it is given its turn, so a call of it that waits
// for nothing makes its next event (`proceeds`). Of what is outside the code: a call is responded to (`responds`).
// Nothing happens in time without these: an execution in which every thread stops for good is one of the code.

val startThreadProceeds = Node.assumption(
  "A call of startThread, pending and waiting for no call it made, makes its next event in time.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code]) => starting(h, code).proceeds))

val aForkFunctionProceeds = Node.assumption(
  "A call of a function startThread handed a thread factory, pending and waiting for no call it made, makes " +
    "its next event in time.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], code: Obj[Code]) =>
    forkFunction(r, h, code) implies running(r).proceeds))

val currentThreadResponds = Node.assumption("A call of `Thread.currentThread()` is responded to, in time.")(
  Thread.currentThread().responds)

val removingResponds = Node.assumption("A call that removes from a concurrent set is responded to, in time.")(
  forall((s: Obj[ConcurrentSet], x: Obj[AnyRef]) => s.remove(x).responds))

val discardResponds = Node.assumption("A call of Ox's `discard` is responded to, in time.")(
  forall((x: Obj[AnyRef]) => ox.discard(x).responds))

// Of the thread factory a herd is given, and of who schedules threads: the thread it makes for a function runs
// that function, once started.
val aStartedThreadRunsItsFunction = Node.assumption(
  "A thread a factory made for a function calls the function in time, once start is called on it.")(
  forall((f: Obj[ThreadFactory], r: Obj[Runnable], t: Obj[Thread]) =>
    forall((a: Term[BigInt], b: Term[BigInt], s: Term[BigInt]) =>
      (f.newThread(r).completed(a, Returned(t), b) && t.start().called(s)) implies
        exists((i: Term[BigInt]) => a < i && running(r).by(t).called(i)))))

// Of who uses Ox: the code given to a fork ends when its thread is interrupted, whenever that was.
val forkCodeCompletesOnceInterrupted = Node.assumption(
  "The code a fork was made to run, called by the fork, is responded to in time, once the fork has been " +
    "interrupted.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], code: Obj[Code], made: Term[BigInt], m: Term[BigInt]) =>
    (madeToRun(t, h, code, made) && code().by(t).called(m) && interrupted(t)) implies
      code().by(t).respondedTo(m)))
