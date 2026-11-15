package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.internal.ThreadHerd

// What Ox's `ThreadHerd` does, each said of one of its methods, and what is assumed of who calls it.

// With capture checking this would be what the compiler says of a capability, not an assumption.
val startThreadIsCalledFromInside = Node.assumption(
  "A thread of a herd is started only by a thread inside its scope: its owner before closing, or a fork that " +
    "has not left.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], w: Term[BigInt]) =>
    starting(h, code).by(c).called(w) implies inside(c, h, w)))

// With capture checking this would be what the compiler says: the set is the herd's alone.
val onlyStartThreadAddsToTheSet = Node.assumption(
  "A thread is added to a herd's set only by a call of startThread on the herd, itself.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], c: Obj[Thread], w: Term[BigInt]) =>
    threads(h).add(t).by(c).called(w) implies
      exists((code: Obj[Code], from: Term[BigInt]) =>
        starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, w))))

val startThreadAddsWhileItRuns = Node.claim(
  "A call of startThread that itself adds a thread has not completed when it does.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], w: Term[BigInt]) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, w)) implies
        starting(h, code).by(c).pendingAt(w))))

val startThreadIsPendingWhileItAdds = Node.claim(
  "A call of startThread has not completed while an add it itself made is pending.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], a: Term[BigInt], w: Term[BigInt]) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, a) &&
        threads(h).add(t).by(c).pendingSince(a, w)) implies starting(h, code).by(c).pendingSince(from, w))))

// Not proven of the code. That the set is made by `newKeySet` is of the herd's constructor, which no execution
// here has: a herd is made by code that is not read. That nothing else is called on it is of who can reach a
// private field: with capture checking it is what the compiler would say.
val aHerdsSetIsPlain = Node.claim(
  "A herd's set is one made by newKeySet, on which nothing but add, remove, isEmpty and forEach is called.")(
  forall((h: Obj[ThreadHerd], w: Term[BigInt]) => h.isMade(w) implies plainSet(threads(h))))

// With capture checking this would be what the compiler says: the thread is a local of startThread, given to
// the herd's set and to nothing else.
val onlyItsMakerStartsAThread = Node.assumption(
  "A thread that a factory made for a call of startThread is started only by that call, itself.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], b: Term[BigInt], m: Term[BigInt], other: Obj[Thread]) =>
      (starting(h, code).by(c).called(from) && madeFor(t, c, from, b) && t.start().by(other).called(m)) implies
        t.start().by(c).calledInside(from, m))))

val startThreadAddsWhatItsFactoryMade = Node.claim(
  "A call of startThread itself adds to the herd's set only a thread that a factory has made for it.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], w: Term[BigInt]) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, w)) implies
        madeFor(t, c, from, w))))

val startThreadAddsBeforeItStarts = Node.claim(
  "A call of startThread itself adds a thread only before it itself starts one.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Term[BigInt], w: Term[BigInt], m: Term[BigInt], started: Obj[Thread]) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, w) &&
        started.start().by(c).calledInside(from, m)) implies (w < m))))

val anAddedThreadHasNotBeenStarted = Node.claim("A thread has not been started when it is added to a herd's set.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], c: Obj[Thread], w: Term[BigInt]) =>
    threads(h).add(t).by(c).called(w) implies !t.start().calledBefore(w)))

val onlyStartThreadAdds = Node.claim(
  "A thread is added to a herd's set only during a call of startThread, by its caller, and has not been started.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], c: Obj[Thread], w: Term[BigInt]) =>
    threads(h).add(t).by(c).called(w) implies
      (exists((code: Obj[Code]) => starting(h, code).by(c).pendingAt(w)) && !t.start().calledBefore(w))))

// With capture checking this would be what the compiler says: the set is the herd's alone, and is given to
// nothing but the functions startThread makes.
val onlyAForkFunctionRemoves = Node.assumption(
  "A thread is removed from a herd's set only by a function that startThread handed the herd's factory, itself.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], c: Obj[Thread], w: Term[BigInt]) =>
    threads(h).remove(t).by(c).called(w) implies
      exists((r: Obj[Runnable], i: Term[BigInt]) =>
        handedOver(r, h, i) && running(r).by(c).called(i) && threads(h).remove(t).by(c).calledInside(i, w))))

val theForkFunctionRemovesTheCurrentThread = Node.claim(
  "The function startThread hands the factory removes from the herd's set, itself, only the thread that " +
    "`Thread.currentThread()` has just given it.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], c: Obj[Thread], t: Obj[Thread]) =>
    forall((i: Term[BigInt], w: Term[BigInt]) =>
      (handedOver(r, h, i) && running(r).by(c).called(i) && threads(h).remove(t).by(c).calledInside(i, w)) implies
        exists((a: Term[BigInt], b: Term[BigInt]) =>
          i < a && b <= w && Thread.currentThread().by(c).completed(a, Returned(t), b)))))

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
