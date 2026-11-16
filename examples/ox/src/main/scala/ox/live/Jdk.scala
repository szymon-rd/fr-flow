package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
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
