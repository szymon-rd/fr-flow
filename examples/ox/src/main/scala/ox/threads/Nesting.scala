package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import java.util.concurrent.atomic.AtomicBoolean
import ox.internal.ThreadHerd

// What a thread calls while it is calling startThread. What the herd's own code calls is proven of the code, call
// by call; what it calls outside itself (the JDK, the herd's factory) is assumed to stay out of herds; a thread
// doing one thing at a time, the two add up.

/** The herd's check that it is not closing, which only its own code may name. */
def closingCheck(h: Obj[ThreadHerd]): Call[Unit] = h.method[Unit]("assertNotShuttingDown")

/** The herd's check that its caller is in the tree of scopes. */
def treeCheck(h: Obj[ThreadHerd]): Call[Unit] = h.method[Unit]("verifyCurrentThreadInScopeTree")

/** While a call of `call` is pending, its caller neither closes a herd nor removes a thread from a herd's set. */
def staysOutOfHerds[A](call: Call[A])(using Stating): Term[Boolean] =
  forall((h: Obj[ThreadHerd], x: Obj[Thread]) => call.excludes(closing(h)) && call.excludes(threads(h).remove(x)))

val startThreadCallsFive = Node.claim(
  "A call of startThread itself calls only the herd's two checks, newThread of a factory, add on a set and " +
    "start of a thread.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code]) =>
    starting(h, code).itselfCallsOnly(made =>
      closingCheck(h).isCall(made) || treeCheck(h).isCall(made) ||
        exists((f: Obj[ThreadFactory], r: Obj[Runnable]) => f.newThread(r).isCall(made)) ||
        exists((s: Obj[ConcurrentSet], t: Obj[Thread]) => s.add(t).isCall(made)) ||
        exists((t: Obj[Thread]) => t.start().isCall(made)))))

val theClosingCheckCallsGet = Node.claim("A call of assertNotShuttingDown itself calls only get of an atomic flag.")(
  forall((h: Obj[ThreadHerd]) =>
    closingCheck(h).itselfCallsOnly(made => exists((b: Obj[AtomicBoolean]) => b.get().isCall(made)))))

// Of the JDK: none of the three calls back into Ox. Adding a thread asks its hashCode and equals, which are
// `Object`'s.
val theJdkStaysOutOfHerds = Node.assumption(
  "While a thread reads an atomic flag, adds a thread to a concurrent set or starts a thread, it neither closes " +
    "a herd nor removes a thread from a herd's set.")(
  forall((b: Obj[AtomicBoolean], s: Obj[ConcurrentSet], t: Obj[Thread]) =>
    staysOutOfHerds(b.get()) && staysOutOfHerds(s.add(t)) && staysOutOfHerds(t.start())))

// Of the factory a herd is given: it makes a thread, and neither runs the function it is handed nor reaches
// a herd.
val aFactoryStaysOutOfHerds = Node.assumption(
  "While a thread factory is making a thread, its caller neither closes a herd nor removes a thread from a " +
    "herd's set.")(
  forall((f: Obj[ThreadFactory], r: Obj[Runnable]) => staysOutOfHerds(f.newThread(r))))

val theClosingCheckStaysOutOfHerds = Node.claim(
  "While a thread is calling assertNotShuttingDown of a herd, it neither closes a herd nor removes a thread " +
    "from a herd's set.")(
  forall((h: Obj[ThreadHerd]) => staysOutOfHerds(closingCheck(h))))

// Not proven of the code. The check reads the scope of the current thread and asks each scope up the tree for
// its herd and its parent: calls on objects of classes not read here.
val theTreeCheckStaysOutOfHerds = Node.claim(
  "While a thread is calling verifyCurrentThreadInScopeTree of a herd, it neither closes a herd nor removes a " +
    "thread from a herd's set.")(
  forall((h: Obj[ThreadHerd]) => staysOutOfHerds(treeCheck(h))))

val startThreadStaysOutOfHerds = Node.claim(
  "While a thread is calling startThread of a herd, it neither closes a herd nor removes a thread from a herd's " +
    "set.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code]) => staysOutOfHerds(starting(h, code))))
