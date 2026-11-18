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
  exists((c: Obj[Thread], from: Moment, f: Obj[ThreadFactory], m: Moment) =>
    starting(h, code).by(c).called(from) && f.newThread(r).by(c).calledInside(from, m)) }

/** The thread has been interrupted: a call of `interrupt` on it has returned. */
val interrupted = stated { (t: Obj[Thread]) => exists((w: Moment) => t.interrupt().returnedBefore(w)) }

/** From some moment on, nothing is added to the set. */
val addingStops = stated { (s: Obj[ConcurrentSet]) =>
  exists((last: Moment) =>
    forall((y: Obj[AnyRef], w: Moment) => (last <= w) implies !s.add(y).called(w))) }

/** From some moment on, no call that adds to the set is in progress: none is made, and each made before is over. */
val addingEnds = stated { (s: Obj[ConcurrentSet]) =>
  exists((last: Moment) =>
    forall((y: Obj[AnyRef], w: Moment) => (last <= w) implies !s.add(y).inProgress(w))) }

/** Nothing is in the set from `empty` on, and no call that removes from it, made before `empty`, is pending at
  * `rest`.
  */
val emptyFrom = stated { (s: Obj[ConcurrentSet], empty: Moment, rest: Moment) =>
  forall((y: Obj[AnyRef], w: Moment) =>
    ((empty <= w) implies !elements(s, w).contains(y.asValue)) &&
      ((w < empty) implies !s.remove(y).pendingSince(w, rest))) }

/** From a moment on nothing is in the set, and by a later one each call that was removing from it before is over:
  * a call that removes from a set that holds nothing takes nothing out.
  */
val restsEmpty = stated { (s: Obj[ConcurrentSet]) =>
  exists((empty: Moment, rest: Moment) => empty <= rest && emptyFrom(s, empty, rest)) }
