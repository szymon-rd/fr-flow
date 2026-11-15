package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.atomic.AtomicBoolean

// What is assumed of the JVM: of the run, and of the methods of the JDK that Ox calls.

/** What is in a concurrent set at a moment. It is no member of the JDK's: it is what the assumptions speak of. */
val elements = Declaration[(Ref[Threads], BigInt) => Set[Value]]("what is in the set at a moment")

val nothingBeforeTheStart = Node.assumption("No step is taken before the run starts.")(
  forall((w: Term[BigInt]) => (w < 0) implies (history(w) === Event.Stutter)))

/** What an atomic boolean holds at a moment. */
val flag = Declaration[(Ref[AtomicBoolean], BigInt) => Boolean]("what the atomic boolean holds at a moment")

val setCallsAreAtomic = Node.assumption("Adding to a concurrent set and removing from it are each atomic.")(
  forall((s: Obj[Threads], x: Obj[Thread]) => s.add(x).atomic && s.remove(x).atomic))

val addPutsItIn = Node.assumption("Adding an element puts it in the set.")(
  forall((s: Obj[Threads], x: Obj[Thread], y: Term[Value]) =>
    s.add(x).everyCall((from, _, to) =>
      elements(s, to).contains(y) === (y === x.asValue || elements(s, from).contains(y)))))

val removeTakesOnlyItOut = Node.assumption("Removing an element takes that element out of the set, and no other.")(
  forall((s: Obj[Threads], x: Obj[Thread], y: Term[Value]) =>
    s.remove(x).everyCall((from, _, to) =>
      elements(s, to).contains(y) === (y =!= x.asValue && elements(s, from).contains(y)))))

// Said of the calls Ox makes on a herd's set: the JDK has others that change a set, which Ox does not call on it.
val onlyAddAndRemoveChangeASet = Node.assumption(
  "What is in a set changes only when an element is added to it or removed from it.")(
  forall((s: Obj[Threads], a: Term[BigInt], b: Term[BigInt], y: Term[Value]) =>
    (a < b && (elements(s, a).contains(y) =!= elements(s, b).contains(y))) implies
      exists((x: Obj[Thread]) => s.add(x).completedWithin(a, b) || s.remove(x).completedWithin(a, b))))

val getGivesTheFlag = Node.assumption("Reading an atomic boolean gives what it holds at a moment during the read.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) =>
    s.get().everyCall((from, a, to) =>
      (a === Returned(b)) implies exists((m: Term[BigInt]) => from <= m && m < to && (flag(s, m) === b)))))

val setMakesTheFlag = Node.assumption("Once a call that sets an atomic boolean completes, it holds what was set.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) => s.set(b).everyCall((_, _, to) => flag(s, to) === b)))

val currentThreadIsTheCaller = Node.assumption("`Thread.currentThread()` gives the thread that calls it.")(
  forall((c: Obj[Thread]) => Thread.currentThread().by(c).everyCall((_, a, _) => a === Returned(c))))

// Said of the calls Ox makes on a herd's flag: the JDK has others that change an atomic boolean.
val aFlagChangesOnlyWhenSet = Node.assumption(
  "What an atomic boolean holds becomes a value only after a call that sets it to that value is made.")(
  forall((s: Obj[AtomicBoolean], v: Term[Boolean], a: Term[BigInt], b: Term[BigInt]) =>
    (a < b && (flag(s, a) =!= v) && (flag(s, b) === v)) implies s.set(v).calledBefore(b)))

val setReturns = Node.assumption("Setting an atomic boolean does not throw.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) => s.set(b).everyCall((_, a, _) => a === Returned(()))))

val isEmptyReturns = Node.assumption("Asking a concurrent set whether it is empty does not throw.")(
  forall((s: Obj[Threads]) =>
    s.isEmpty().everyCall((_, a, _) => (a === Returned(True)) || (a === Returned(False)))))

// `isEmpty` is no snapshot: it sums counters read one after another (`ConcurrentHashMap.sumCount`), and the JDK
// says its answer is for use only where no other thread changes the set meanwhile. What is assumed is what that
// sum gives when nothing is added during the call: every element is counted before it, and elements only leave.
val isEmptyFindsItEmptyUnlessAdded = Node.assumption(
  "A concurrent set that answers that it is empty, with nothing added to it during the call, is empty at a " +
    "moment during the call.")(
  forall((s: Obj[Threads]) =>
    s.isEmpty().everyCall((from, a, to) =>
      ((a === Returned(True)) && !addedDuring(s, from, to)) implies exists((m: Term[BigInt]) =>
        from <= m && m <= to && forall((y: Term[Value]) => !elements(s, m).contains(y))))))
