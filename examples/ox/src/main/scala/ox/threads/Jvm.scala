package ox.threads

import frflow.{Call as _, *}
import frflow.runs.*
import frflow.runs.InCode.given

// What is assumed of the JVM: of the run, and of the methods of the JDK that Ox calls.

/** What is in a concurrent set at a moment. It is no member of the JDK's: it is what the assumptions speak of. */
val elements = Declaration[(Ref[Threads], BigInt) => Set[Thing]]("what is in the set at a moment")

val nothingBeforeTheStart = Node.assumption("No step is taken before the run starts.")(
  forall((w: Term[BigInt]) => (w < 0) implies (steps(w) === Step.Rests)))

val setCallsAreAtomic = Node.assumption("Adding to a concurrent set and removing from it are each atomic.")(
  forall((s: Obj[Threads], x: Obj[Thread]) => s.add(x).atomic && s.remove(x).atomic))

val addPutsItIn = Node.assumption("Adding an element puts it in the set.")(
  forall((s: Obj[Threads], x: Obj[Thread], y: Term[Thing]) =>
    s.add(x).everyCall((from, _, to) =>
      elements(s, to).contains(y) === (y === x.thing || elements(s, from).contains(y)))))

val removeTakesOnlyItOut = Node.assumption("Removing an element takes that element out of the set, and no other.")(
  forall((s: Obj[Threads], x: Obj[Thread], y: Term[Thing]) =>
    s.remove(x).everyCall((from, _, to) =>
      elements(s, to).contains(y) === (y =!= x.thing && elements(s, from).contains(y)))))

// Said of the calls Ox makes on a herd's set: the JDK has others that change a set, which Ox does not call on it.
val onlyAddAndRemoveChangeASet = Node.assumption(
  "What is in a set changes only when an element is added to it or removed from it.")(
  forall((s: Obj[Threads], a: Term[BigInt], b: Term[BigInt], y: Term[Thing]) =>
    (a < b && (elements(s, a).contains(y) =!= elements(s, b).contains(y))) implies
      exists((x: Obj[Thread]) => s.add(x).completedWithin(a, b) || s.remove(x).completedWithin(a, b))))
