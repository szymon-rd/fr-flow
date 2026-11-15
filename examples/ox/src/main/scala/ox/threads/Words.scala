package ox.threads

import frflow.{Call as _, *}
import frflow.runs.*
import frflow.runs.InCode.given
import java.util.concurrent.ConcurrentHashMap
import ox.internal.ThreadHerd

// The words of the model: a herd's set and its owner, and what a thread is to a herd. Every word is said of calls
// of Ox's own code and of the JDK.

/** The set a herd keeps its threads in. */
type Threads = ConcurrentHashMap.KeySetView[Thread, java.lang.Boolean]

/** Code given to run: what `startThread` and a fork function take. */
type Code = () => Unit

def threads(h: Obj[ThreadHerd])(using Stating): Obj[Threads] = h.field("threads")
def owner(h: Obj[ThreadHerd])(using Stating): Obj[Thread] = h.field("herdOwner")

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

/** Nothing is in the herd's set. */
val empty = stated { (h: Obj[ThreadHerd], w: Term[BigInt]) =>
  forall((y: Term[Thing]) => !elements(threads(h), w).contains(y)) }
