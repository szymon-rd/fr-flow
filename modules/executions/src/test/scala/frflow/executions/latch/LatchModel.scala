package frflow.executions.latch

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.atomic.AtomicBoolean

// A model of code read from its TASTy: `Latch`, as it is compiled. What is claimed of `enter` at the bottom is
// proven of the tree read, from what is assumed of the JVM.

/** The latch's flag. */
def closed(l: Obj[Latch])(using Stating): Obj[AtomicBoolean] = l.field("closed")

/** What an atomic boolean holds at a moment. */
val flag = Declaration[(Ref[AtomicBoolean], BigInt) => Boolean]("what the atomic boolean holds at a moment")

val enterIsCalledOnALatch = Node.assumption("`enter` is called only on a latch that has been made.")(
  forall((l: Obj[Latch], w: Term[BigInt]) => l.enter().called(w) implies l.isMade(w)))

val aLatchKeepsItsFlag = Node.assumption("A latch's flag is read as the flag it holds.")(
  forall((l: Obj[Latch]) => l.readsAsHeld("closed")))

val getGivesTheFlag = Node.assumption("Reading an atomic boolean gives what it holds at a moment during the read.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) =>
    s.get().everyCall((from, a, to) =>
      (a === Returned(b)) implies exists((m: Term[BigInt]) => from <= m && m < to && (flag(s, m) === b)))))

val enterReadsItOpen = Node.claim("`enter` returns only after it has read the latch's flag as unset.")(
  forall((l: Obj[Latch]) =>
    l.enter().everyCall((from, a, to) =>
      (a === Returned(())) implies closed(l).get().returnedWithin(False, from, to))))

val enterFindsItOpen = Node.claim("`enter` returns only if the latch's flag was unset at a moment during the call.")(
  forall((l: Obj[Latch]) =>
    l.enter().everyCall((from, a, to) =>
      (a === Returned(())) implies exists((m: Term[BigInt]) => from <= m && m < to && !flag(closed(l), m)))))

val latch: FrModel = FrModel("Latch")(
  enterFindsItOpen,
  enterReadsItOpen.refines(enterFindsItOpen), getGivesTheFlag.refines(enterFindsItOpen),
  enterIsCalledOnALatch.refines(enterReadsItOpen), aLatchKeepsItsFlag.refines(enterReadsItOpen),
  history.executing(Read.of(classOf[Latch], _.endsWith("latch/Latch.tasty"))))
