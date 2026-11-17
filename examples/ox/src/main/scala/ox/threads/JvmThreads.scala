package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.function.Consumer

// What is assumed of the JDK's threads, of what it throws, and of a traversal of a concurrent set.

val aThreadDoesOneThingAtATime = Node.assumption(
  "A thread does one thing at a time: what it does while a call of its own is pending is done by that call " +
    "itself, or while a call that call itself made is pending.")(
  forall((t: Obj[Thread]) => oneAtATime(t.asValue)))

val aTraversalThrowsOnlyWhatItsFunctionThrew = Node.assumption(
  "A traversal of a concurrent set with a function returns, or throws what a call of the function that it " +
    "itself made during it threw.")(
  forall((s: Obj[ConcurrentSet], f: Obj[Consumer[AnyRef]], c: Obj[Thread]) =>
    (f.asValue =!= noObject) implies
      s.forEach(f).by(c).everyCall((from, r, to) =>
        r === Returned(()) || exists((x: Obj[AnyRef], e: Term[Value], a: Term[BigInt], b: Term[BigInt]) =>
          from < a && b <= to && r === make[Response.Threw](e) && f.accept(x).by(c).calledInside(from, a) &&
            f.accept(x).by(c).completed(a, make[Response.Threw](e), b)))))

val joinThrowsOnlyAnInterruption = Node.assumption(
  "A call of join on a thread returns, or throws an InterruptedException.")(
  forall((t: Obj[Thread]) =>
    t.join().everyCall((_, r, _) => r === Returned(()) || r === Threw(thrown[InterruptedException]))))

// With no security manager to refuse it: none can be installed from JDK 24 on, and before that only if the JVM is
// started to allow one. Of `Thread`'s own `interrupt`, which a class of threads can override.
val interruptReturns = Node.assumption("A call of interrupt on a thread returns.")(
  forall((t: Obj[Thread]) => t.interrupt().everyCall((_, r, _) => r === Returned(()))))

// The JDK refuses an exception given itself. An execution does not tell two exceptions of the JDK of one class
// apart; in the JVM two that `join` threw are two objects, so the call the code makes is never that one.
val addSuppressedReturns = Node.assumption(
  "A call of addSuppressed on an exception, given an InterruptedException the JDK threw, returns.")(
  forall((x: Obj[Throwable]) =>
    (x.asValue =!= noObject) implies
      x.addSuppressed(thrown[InterruptedException]).everyCall((_, r, _) => r === Returned(()))))
