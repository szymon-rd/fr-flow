package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.function.Consumer
import ox.internal.ThreadHerd
import ox.threads.*

// That a herd's set empties: closing interrupts each thread that stays in it, and each leaves for good.

/** Closing has traversed the herd's set, from `a` to `b`, with no call adding to the set in progress from `a` on. */
val traversedWithNoneAdding = stated { (h: Obj[ThreadHerd], a: Term[BigInt], b: Term[BigInt]) =>
  exists((f: Obj[Consumer[AnyRef]], from: Term[BigInt], r: Term[Response]) =>
    closing(h).by(owner(h)).called(from) && threads(h).forEach(f).by(owner(h)).calledInside(from, a) &&
      threads(h).forEach(f).by(owner(h)).completed(a, r, b) &&
      forall((y: Obj[AnyRef], w: Term[BigInt]) => (a <= w) implies !threads(h).add(y).inProgress(w))) }

// The JDK's `ConcurrentHashMap`: its traversals are weakly consistent, and go through each element that is in
// the map from their start to their end.
val aTraversalReachesWhatStays = Node.assumption(
  "A traversal of a concurrent set that returns has applied its function to each element that was in the set " +
    "from its call to its return.")(
  forall((s: Obj[ConcurrentSet], f: Obj[Consumer[AnyRef]], c: Obj[Thread], x: Obj[AnyRef]) =>
    forall((from: Term[BigInt], to: Term[BigInt]) =>
      (s.forEach(f).by(c).completed(from, Returned(()), to) &&
        forall((w: Term[BigInt]) => (from <= w && w <= to) implies elements(s, w).contains(x.asValue))) implies
        exists((m: Term[BigInt]) => from < m && f.accept(x).by(c).calledInside(from, m)))))

val closingsFunctionsInterrupt = Node.claim(
  "Once a function closing has passed to a traversal has completed on a thread, the thread has been interrupted.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[AnyRef]], x: Obj[Thread], c: Obj[Thread]) =>
    forall((k: Term[BigInt], r: Term[Response], b: Term[BigInt]) =>
      (traversedWith(f, h, k) && f.accept(x.seenAs[AnyRef]).by(c).completed(k, r, b)) implies
        x.interrupt().returnedBefore(b))))

val whatStaysInATraversedSetIsInterrupted = Node.claim(
  "A thread in a herd's set after closing has traversed it, with no call adding to it in progress, has been " +
    "interrupted.")(
  forall((h: Obj[ThreadHerd], x: Obj[Thread], a: Term[BigInt], b: Term[BigInt], w: Term[BigInt]) =>
    forall((made: Term[BigInt]) =>
      (h.isConstructed(made) && traversedWithNoneAdding(h, a, b) && b <= w &&
        elements(threads(h), w).contains(x.asValue)) implies interrupted(x))))

val aHerdsSetEmptiesOnceTraversed = Node.claim(
  "A herd's set comes to rest empty, once closing has traversed it with no call adding to it in progress.")(
  forall((h: Obj[ThreadHerd], made: Term[BigInt]) => h.isConstructed(made) implies emptiesOnceTraversed(h)))

val closingCompletes = Node.claim("A call of closing on a herd by its owner is responded to, in time.")(
  forall((h: Obj[ThreadHerd], from: Term[BigInt]) =>
    closing(h).by(owner(h)).called(from) implies closing(h).by(owner(h)).respondedTo(from)))
