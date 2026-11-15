package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.{ConcurrentHashMap, ThreadFactory}
import java.util.concurrent.atomic.AtomicBoolean
import ox.internal.ThreadHerd

// The words of the model: a herd's set and its owner, and what a thread is to a herd. Every word is said of calls
// of Ox's own code and of the JDK.

/** A concurrent set of objects, as the JDK has it: what is assumed of one is assumed of any, whatever it holds. */
type ConcurrentSet = ConcurrentHashMap.KeySetView[AnyRef, java.lang.Boolean]

/** Code given to run: what `startThread` and a fork function take. */
type Code = () => Unit

/** The set a herd keeps its threads in. */
def threads(h: Obj[ThreadHerd])(using Stating): Obj[ConcurrentSet] = h.field("threads").seenAs[ConcurrentSet]
def owner(h: Obj[ThreadHerd])(using Stating): Obj[Thread] = h.field("herdOwner")

def shutdown(h: Obj[ThreadHerd])(using Stating): Obj[AtomicBoolean] = h.field("shutdownInProgress")
def factory(h: Obj[ThreadHerd])(using Stating): Obj[ThreadFactory] = h.field("threadFactory")

/** Closing a herd: interrupting its threads and waiting until none is left. */
def closing(h: Obj[ThreadHerd])(using Stating): Call[Unit] = h.interruptAllAndJoinUntilCompleted()

/** Starting a thread of the herd to run the code. */
def starting(h: Obj[ThreadHerd], code: Obj[Code])(using Stating): Call[Unit] = h.startThread(code.byName)

/** The thread is a fork of the herd: the herd has added it to its set. */
val forkOf = stated { (t: Obj[Thread], h: Obj[ThreadHerd], w: Term[BigInt]) => threads(h).add(t).calledBefore(w) }

/** The fork has left: it has been taken out of the set. */
val hasLeft = stated { (t: Obj[Thread], h: Obj[ThreadHerd], w: Term[BigInt]) => threads(h).remove(t).calledBefore(w) }

/** The fork has not left. */
val live = stated { (t: Obj[Thread], h: Obj[ThreadHerd], w: Term[BigInt]) => forkOf(t, h, w) && !hasLeft(t, h, w) }

/** The fork was made to run the code: its thread was added during `startThread(code)`, by its caller. */
val madeToRun = stated { (t: Obj[Thread], h: Obj[ThreadHerd], code: Obj[Code], w: Term[BigInt]) =>
  exists((c: Obj[Thread], m: Term[BigInt]) =>
    m < w && threads(h).add(t).by(c).called(m) && starting(h, code).by(c).pendingAt(m)) }

/** Closing the herd, by its owner, has completed. */
val closed = stated { (h: Obj[ThreadHerd], w: Term[BigInt]) =>
  closing(h).by(owner(h)).calledBefore(w) && !closing(h).by(owner(h)).pendingAt(w) }

/** The thread is inside the herd's scope: its owner before it calls closing, or a fork of it that has not left. */
val inside = stated { (c: Obj[Thread], h: Obj[ThreadHerd], w: Term[BigInt]) =>
  (c === owner(h) && !closing(h).by(owner(h)).calledBefore(w)) || live(c, h, w) }

/** An element is being added to the set at some moment from `from` to `to`: a call that adds is pending at
  * `from`, or is made before `to`.
  */
val addedDuring = stated { (s: Obj[ConcurrentSet], from: Term[BigInt], to: Term[BigInt]) =>
  exists((x: Obj[AnyRef]) => s.add(x).pendingAt(from) || s.add(x).calledWithin(from, to)) }

/** Nothing is in the herd's set. */
val empty = stated { (h: Obj[ThreadHerd], w: Term[BigInt]) =>
  forall((y: Term[Value]) => !elements(threads(h), w).contains(y)) }

/** A thread running the function: `r.run()`, named as the JDK names it (a term's own `run` hides the method). */
def running(r: Obj[Runnable]): Call[Unit] = Call.of[Unit]("java.lang.Runnable run :scala.Unit", r.asValue)

/** The function was handed to the herd's factory, by a call of startThread on the herd itself, before the
  * moment: it is what a thread of the herd runs.
  */
val handedOver = stated { (r: Obj[Runnable], h: Obj[ThreadHerd], w: Term[BigInt]) =>
  exists((code: Obj[Code], c: Obj[Thread], from: Term[BigInt], m: Term[BigInt]) =>
    m < w && starting(h, code).by(c).called(from) && factory(h).newThread(r).by(c).calledInside(from, m)) }

/** The thread was made by a thread factory, for the call of startThread made at `from` by `c` itself, by the
  * moment `b`.
  */
val madeFor = stated { (t: Obj[Thread], c: Obj[Thread], from: Term[BigInt], b: Term[BigInt]) =>
  exists((f: Obj[ThreadFactory], r: Obj[Runnable], a: Term[BigInt], done: Term[BigInt]) =>
    done <= b && f.newThread(r).by(c).calledInside(from, a) &&
      f.newThread(r).by(c).completed(a, Returned(t), done)) }
