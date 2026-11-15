package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.internal.ThreadHerd

// The herd's flag. What `startThread` and closing do with it is proven of `ThreadHerd`'s tree, read from Ox's
// TASTy; what that gives once the herd is closed follows from what is assumed of an atomic boolean.

val herdsAreMade = Node.assumption("startThread and closing are called only on a herd that has been made.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], w: Term[BigInt]) =>
    (starting(h, code).called(w) || closing(h).called(w)) implies h.isMade(w)))

val aHerdKeepsItsFields = Node.assumption("A herd's flag, its set and its owner are read as what the herd holds.")(
  forall((h: Obj[ThreadHerd]) =>
    h.readsAsHeld("shutdownInProgress") && h.readsAsHeld("threads") && h.readsAsHeld("herdOwner")))

val startThreadReadsTheFlagUnset = Node.claim(
  "A call of startThread adds a thread, or returns, only after it has read the herd's flag as unset.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], w: Term[BigInt]) =>
      (starting(h, code).by(c).called(from) && (threads(h).add(t).by(c).calledInside(from, w) ||
        starting(h, code).by(c).completed(from, Returned(()), w))) implies
        shutdown(h).get().returnedWithin(False, from, w))))

val startThreadFirstSeesTheFlagUnset = Node.claim(
  "A call of startThread adds a thread, or returns, only after a moment, during it, at which the flag is unset.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], w: Term[BigInt]) =>
      (starting(h, code).by(c).called(from) && (threads(h).add(t).by(c).calledInside(from, w) ||
        starting(h, code).by(c).completed(from, Returned(()), w))) implies
        exists((m: Term[BigInt]) => from <= m && m < w && !flag(shutdown(h), m)))))

val closingSetsTheFlagItself = Node.claim(
  "Closing a herd, by its owner, completes only after it has set the herd's flag.")(
  forall((h: Obj[ThreadHerd]) =>
    closing(h).by(owner(h)).everyCall((from, _, to) => shutdown(h).set(True).completedWithin(from, to))))

val closingSetsTheFlag = Node.claim("When closing a herd completes, the herd's flag is set.")(
  forall((h: Obj[ThreadHerd]) =>
    closing(h).by(owner(h)).everyCall((_, _, to) => flag(shutdown(h), to))))

val theFlagStaysSet = Node.claim("Once a herd's flag is set, it stays set.")(
  forall((h: Obj[ThreadHerd], a: Term[BigInt], b: Term[BigInt]) =>
    (a < b && flag(shutdown(h), a)) implies flag(shutdown(h), b)))

// With capture checking this would be what the compiler says of a capability, not an assumption.
val onlyClosingSetsTheFlag = Node.assumption("A herd's flag is set only by a call of closing, itself.")(
  forall((h: Obj[ThreadHerd], v: Term[Boolean], c: Obj[Thread], w: Term[BigInt]) =>
    shutdown(h).set(v).by(c).called(w) implies exists((from: Term[BigInt]) =>
      closing(h).by(c).called(from) && shutdown(h).set(v).by(c).calledInside(from, w))))

// Not proven of the code: past its loop, closing reads a local variable and may throw what it holds, and what a
// local variable holds is not yet said of an execution.
val closingSetsTheFlagOnlyToTrue = Node.claim("A call of closing itself sets the herd's flag only to true.")(
  forall((h: Obj[ThreadHerd], v: Term[Boolean], c: Obj[Thread], from: Term[BigInt], w: Term[BigInt]) =>
    (closing(h).by(c).called(from) && shutdown(h).set(v).by(c).calledInside(from, w)) implies v))
