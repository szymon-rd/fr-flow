package frflow.executions.sets

import frflow.*
import frflow.executions.*
import frflow.values.*

// A concurrent set as its assumptions say it, and what follows of what is in it: no code is read.

val setCallsAreAtomic = Node.assumption("Adding to a concurrent set and removing from it are each atomic.")(
  forall((s: Obj[KeySet], x: Term[Value]) => add(s, x).atomic && remove(s, x).atomic))

val addPutsItIn = Node.assumption("Adding an element puts it in the set.")(
  forall((s: Obj[KeySet], x: Term[Value], y: Term[Value]) =>
    add(s, x).everyCall((from, _, to) =>
      elements(s, to).contains(y) === (y === x || elements(s, from).contains(y)))))

val removeTakesOnlyItOut = Node.assumption("Removing an element takes that element out of the set, and no other.")(
  forall((s: Obj[KeySet], x: Term[Value], y: Term[Value]) =>
    remove(s, x).everyCall((from, _, to) =>
      elements(s, to).contains(y) === (y =!= x && elements(s, from).contains(y)))))

val onlyAddAndRemoveChangeASet = Node.assumption(
  "What is in a set changes only when an element is added to it or removed from it.")(
  forall((s: Obj[KeySet], a: Term[BigInt], b: Term[BigInt], y: Term[Value]) =>
    (a < b && (elements(s, a).contains(y) =!= elements(s, b).contains(y))) implies
      exists((x: Term[Value]) => add(s, x).completedWithin(a, b) || remove(s, x).completedWithin(a, b))))

val nothingBeforeTheStart = Node.assumption("No step is taken before the run starts.")(
  forall((w: Term[BigInt]) => (w < 0) implies (history(w) === Event.Stutter)))

val whoIsAddedStays = Node.claim("What was added to a set and not removed from it is in the set.")(
  forall((s: Obj[KeySet], t: Term[Value], w: Term[BigInt]) =>
    (add(s, t).calledBefore(w) && !remove(s, t).calledBefore(w)) implies elements(s, w).contains(t)))

val sets: FrModel = FrModel("Sets")(whoIsAddedStays,
  setCallsAreAtomic.refines(whoIsAddedStays), addPutsItIn.refines(whoIsAddedStays),
  removeTakesOnlyItOut.refines(whoIsAddedStays), onlyAddAndRemoveChangeASet.refines(whoIsAddedStays),
  nothingBeforeTheStart.refines(whoIsAddedStays))
