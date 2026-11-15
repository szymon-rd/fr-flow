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

val aCallCompletesAfterItIsMade = Node.assumption("A call completes after it is made.")(
  forall((by: Term[Value], made: Term[BigInt], a: Term[Response], spawns: Term[List[Spawn]], k: Term[BigInt]) =>
    (history(k) === make[Event.Respond](by, made, a, spawns)) implies (made < k)))

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
