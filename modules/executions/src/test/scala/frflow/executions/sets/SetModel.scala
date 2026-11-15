package frflow.executions.sets

import frflow.*
import frflow.executions.*
import frflow.values.*

// A concurrent set as its assumptions say it, and what follows of what is in it: no code is read.

val addingIsAtomic = Node.assumption(
  "Adding an element is atomic: at one moment during the call, the element is put in the set.")(
  forall((s: Obj[KeySet], x: Term[Value]) =>
    add(s, x).atomic((before, after) => forall((y: Term[Value]) =>
      elements(s, after).contains(y) === (y === x || elements(s, before).contains(y))))))

val onlyAddAndRemoveChangeASet = Node.assumption(
  "An element enters a set only at a moment during a call that adds it, and leaves it only at a moment during a " +
    "call that removes it.")(
  forall((s: Obj[KeySet], w: Term[BigInt], y: Term[Value]) =>
    ((!elements(s, w).contains(y) && elements(s, w + 1).contains(y)) implies add(s, y).inProgress(w)) &&
      ((elements(s, w).contains(y) && !elements(s, w + 1).contains(y)) implies remove(s, y).inProgress(w))))

val whoIsAddedStays = Node.claim(
  "What a call has added to a set, with no call made to remove it, is in the set.")(
  forall((s: Obj[KeySet], t: Term[Value], w: Term[BigInt]) =>
    (add(s, t).returnedBefore(w) && !remove(s, t).calledBefore(w)) implies elements(s, w).contains(t)))

val sets: FrModel = FrModel("Sets")(whoIsAddedStays,
  addingIsAtomic.refines(whoIsAddedStays), onlyAddAndRemoveChangeASet.refines(whoIsAddedStays))
