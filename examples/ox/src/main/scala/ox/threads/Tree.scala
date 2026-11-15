package ox.threads

import frflow.{Call as _, *}
import frflow.runs.*
import frflow.runs.InCode.given
import ox.internal.ThreadHerd

// What the claims on `ThreadHerd` and the assumptions add up to, up to what holds once a herd is closed.

val liveForksAreInTheSet = Node.claim("A fork that has not left is in its herd's set.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], w: Term[BigInt]) =>
    live(t, h, w) implies elements(threads(h), w).contains(t.thing)))

val startThreadCallersStayInside = Node.claim(
  "While a thread is calling startThread of a herd, it is inside the herd's scope.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], w: Term[BigInt]) =>
    (starting(h, code).by(c).called(w) || starting(h, code).by(c).pendingAt(w)) implies inside(c, h, w)))

val nothingIsAddedOnceEmpty = Node.claim(
  "Once a herd's set is empty after its owner called closing, no thread is added to it.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], m: Term[BigInt], w: Term[BigInt]) =>
    (closing(h).by(owner(h)).calledBefore(m) && empty(h, m) && m <= w) implies !threads(h).add(t).called(w)))

val everyForkHasLeftOnceClosed = Node.claim("After closing a herd has completed, every fork of it has left.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], w: Term[BigInt]) =>
    (closed(h, w) && forkOf(t, h, w)) implies hasLeft(t, h, w)))

val nothingIsAddedOnceClosed = Node.claim("After closing a herd has completed, no thread is added to its set.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], w: Term[BigInt]) =>
    closed(h, w) implies !threads(h).add(t).called(w)))

val noForkRunsOnceClosed = Node.claim(
  "After closing a herd has completed, no fork of it runs the code it was made to run.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], code: Obj[Code], w: Term[BigInt]) =>
    (closed(h, w) && madeToRun(t, h, code, w)) implies
      (!code().by(t).pendingAt(w) && !code().by(t).called(w))))

val aClosedHerdRefusesToStart = Node.claim(
  "After closing a herd has completed, a call of its startThread does not return, and adds no thread.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    starting(h, code).by(c).everyCall((from, answer, to) =>
      closed(h, from) implies
        (answer =!= Returned(()) && !threads(h).add(t).by(c).calledWithin(from, to)))))
