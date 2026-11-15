package ox.threads

import frflow.{Call as _, *}
import frflow.runs.*
import frflow.runs.InCode.given
import ox.internal.ThreadHerd

// What Ox's `ThreadHerd` does, each said of one of its methods, and what is assumed of who calls it.

// With capture checking this would be what the compiler says of a capability, not an assumption.
val startThreadIsCalledFromInside = Node.assumption(
  "A thread of a herd is started only by a thread inside its scope: its owner before closing, or a fork that " +
    "has not left.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], w: Term[BigInt]) =>
    starting(h, code).by(c).called(w) implies inside(c, h, w)))

val onlyStartThreadAdds = Node.claim(
  "A thread is added to a herd's set only during a call of startThread, by its caller, and has not been started.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], c: Obj[Thread], w: Term[BigInt]) =>
    threads(h).add(t).by(c).called(w) implies
      (exists((code: Obj[Code]) => starting(h, code).by(c).pendingAt(w)) && !t.start().calledBefore(w))))

val aForkRemovesOnlyItself = Node.claim("A thread is removed from a herd's set only by itself.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], c: Obj[Thread], w: Term[BigInt]) =>
    threads(h).remove(t).by(c).called(w) implies (c === t)))

val startThreadNeitherClosesNorLeaves = Node.claim(
  "While a thread is calling startThread of a herd, it neither closes the herd nor removes itself from its set.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], w: Term[BigInt]) =>
    starting(h, code).by(c).pendingAt(w) implies
      (!closing(h).by(c).called(w) && !threads(h).remove(c).by(c).called(w))))

// Said of every moment `w` of a run in which the fork is made, whenever in it (`made`).
val codeRunsBeforeLeaving = Node.claim(
  "A fork calls the code it was made to run only before it leaves, and leaves only when no such call is pending.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], code: Obj[Code], made: Term[BigInt], w: Term[BigInt]) =>
    madeToRun(t, h, code, made) implies
      ((code().by(t).called(w) implies !hasLeft(t, h, w)) &&
        (threads(h).remove(t).called(w) implies !code().by(t).pendingAt(w)))))

val closingEndsOnEmpty = Node.claim(
  "Closing a herd completes only after a moment, during it, at which the herd's set is empty.")(
  forall((h: Obj[ThreadHerd]) =>
    closing(h).by(owner(h)).everyCall((from, _, to) =>
      exists((m: Term[BigInt]) => from < m && m <= to && empty(h, m)))))

val closingSetsTheFlag = Node.claim("When closing a herd completes, the herd's flag is set.")(
  forall((h: Obj[ThreadHerd]) =>
    closing(h).by(owner(h)).everyCall((_, _, to) => flag(shutdown(h), to))))

val theFlagStaysSet = Node.claim("Once a herd's flag is set, it stays set.")(
  forall((h: Obj[ThreadHerd], a: Term[BigInt], b: Term[BigInt]) =>
    (a < b && flag(shutdown(h), a)) implies flag(shutdown(h), b)))

val startThreadFirstSeesTheFlagUnset = Node.claim(
  "startThread adds a thread, or returns, only after it has seen the herd's flag unset.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], w: Term[BigInt]) =>
      (starting(h, code).by(c).called(from) && from < w &&
        (threads(h).add(t).by(c).called(w) || starting(h, code).by(c).completed(from, Returned(()), w))) implies
        exists((m: Term[BigInt]) => from <= m && m < w && !flag(shutdown(h), m)))))
