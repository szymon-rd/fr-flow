package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import ox.internal.ThreadHerd
import ox.threads.*

// The words of what happens in time.

/** The function is one a call of `startThread(code)` on the herd itself handed a thread factory. */
val forkFunction = stated { (r: Obj[Runnable], h: Obj[ThreadHerd], code: Obj[Code]) =>
  exists((c: Obj[Thread], from: Term[BigInt], f: Obj[ThreadFactory], m: Term[BigInt]) =>
    starting(h, code).by(c).called(from) && f.newThread(r).by(c).calledInside(from, m)) }

/** The thread has been interrupted: a call of `interrupt` on it has returned. */
val interrupted = stated { (t: Obj[Thread]) => exists((w: Term[BigInt]) => t.interrupt().returnedBefore(w)) }

/** From some moment on, nothing is added to the set. */
val addingStops = stated { (s: Obj[ConcurrentSet]) =>
  exists((last: Term[BigInt]) =>
    forall((y: Obj[AnyRef], w: Term[BigInt]) => (last <= w) implies !s.add(y).called(w))) }

/** From some moment on, no call that adds to the set is in progress: none is made, and each made before is over. */
val addingEnds = stated { (s: Obj[ConcurrentSet]) =>
  exists((last: Term[BigInt]) =>
    forall((y: Obj[AnyRef], w: Term[BigInt]) => (last <= w) implies !s.add(y).inProgress(w))) }

/** From some moment on nothing is in the set, and no call that removes from it is in progress. */
val restsEmpty = stated { (s: Obj[ConcurrentSet]) =>
  exists((rest: Term[BigInt]) =>
    forall((y: Obj[AnyRef], w: Term[BigInt]) =>
      (rest <= w) implies (!elements(s, w).contains(y.asValue) && !s.remove(y).inProgress(w)))) }
