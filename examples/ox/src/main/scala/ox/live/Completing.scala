package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.function.Consumer
import ox.internal.ThreadHerd
import ox.threads.*

// That closing a herd completes: its loop ends once the herd's set rests empty.

/** The herd's set comes to rest empty, once closing has traversed it with no call adding to it in progress. */
val emptiesOnceTraversed = stated { (h: Obj[ThreadHerd]) =>
  forall((f: Obj[Consumer[AnyRef]], from: Term[BigInt], a: Term[BigInt], r: Term[Response], b: Term[BigInt]) =>
    (closing(h).by(owner(h)).called(from) && threads(h).forEach(f).by(owner(h)).calledInside(from, a) &&
      threads(h).forEach(f).by(owner(h)).completed(a, r, b) &&
      forall((y: Obj[AnyRef], w: Term[BigInt]) => (a <= w) implies !threads(h).add(y).inProgress(w))) implies
      restsEmpty(threads(h))) }

val theOwnerCheckResponds = Node.claim("A call of assertOnOwnerThread on a herd is responded to, in time.")(
  forall((h: Obj[ThreadHerd]) => ownerCheck(h).responds))
  .from(aHerdsMethodsProceed, currentThreadResponds, herdsAreMade)

val closingCompletesOnceItsHerdEmpties = Node.claim(
  "A call of closing on a herd by its owner is responded to in time, if the herd's set comes to rest empty once " +
    "closing has traversed it with no call adding to it in progress.")(
  forall((h: Obj[ThreadHerd], from: Term[BigInt]) =>
    (closing(h).by(owner(h)).called(from) && emptiesOnceTraversed(h)) implies
      closing(h).by(owner(h)).respondedTo(from)))
  .from(closingsTraversalsRespond, addingStopsOnceTheFlagIsSet, addingEndsOnceTheFlagIsSet, theOwnerCheckResponds,
    settingResponds, isEmptyResponds, isEmptyFindsARestingSetEmpty, aHerdsMethodsProceed, settingIsAtomic,
    herdsAreConstructed, herdsAreMade, aHerdKeepsItsFields)
