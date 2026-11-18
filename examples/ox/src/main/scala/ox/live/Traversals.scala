package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.function.Consumer
import ox.internal.ThreadHerd
import ox.threads.*

// What closing's traversals do in time, and when adding to a herd's set stops.

val whatIsInAHerdsSetWasMadeToRun = Node.claim(
  "A thread in a herd's set was made to run code: it was added during a call of startThread on the herd.")(
  forall((h: Obj[ThreadHerd], x: Obj[Thread], w: Term[BigInt], b: Term[BigInt]) =>
    (ready(h, b) && elements(threads(h), w).contains(x.asValue)) implies
      exists((code: Obj[Code], made: Term[BigInt]) => madeToRun(x, h, code, made))))
  .from(anElementWasAdded, onlyStartThreadAddsToTheSet, startThreadAddsWhileItRuns, aHerdsSetIsPlain)

val closingsTraversalsRespond = Node.claim(
  "A traversal of the herd's set that closing makes itself is responded to in time, once nothing more is " +
    "added to the set.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[AnyRef]], from: Term[BigInt], a: Term[BigInt]) =>
    (closing(h).by(owner(h)).called(from) && threads(h).forEach(f).by(owner(h)).calledInside(from, a) &&
      addingStops(threads(h))) implies threads(h).forEach(f).by(owner(h)).respondedTo(a)))
  .from(closingsFunctionsRespond, aTraversalRespondsOnceItsFunctionDoes, aTraversalAppliesItsFunctionToElements,
    whatIsInAHerdsSetWasMadeToRun, herdsAreConstructed)

val addingStopsOnceTheFlagIsSet = Node.claim(
  "From some moment on, nothing is added to the set of a herd whose flag is set.")(
  forall((h: Obj[ThreadHerd], w: Term[BigInt]) =>
    (ready(h, w) && flag(shutdown(h), w)) implies addingStops(threads(h))))
  .from(theExecutionBegins, startThreadAddsOnce, theFlagStaysSet, startThreadFirstSeesTheFlagUnset,
    onlyStartThreadAddsToTheSet)

// A call that adds takes time, and what it adds is in the set from a moment during it: so adding has ended only
// when each call that adds is over.
val addingEndsOnceTheFlagIsSet = Node.claim(
  "From some moment on, no call that adds to the set of a herd whose flag is set is in progress.")(
  forall((h: Obj[ThreadHerd], w: Term[BigInt]) =>
    (ready(h, w) && flag(shutdown(h), w)) implies addingEnds(threads(h))))
  .from(addingStopsOnceTheFlagIsSet, addingResponds, theExecutionBegins)
