package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.function.Consumer
import ox.internal.ThreadHerd

// The end of closing: `interruptAllAndJoinUntilCompleted` loops while the herd's set is not empty.

val closingEndsOnceFoundEmpty = Node.claim(
  "Closing a herd completes only after a call it made, asking whether the herd's set is empty, was answered yes.")(
  forall((h: Obj[ThreadHerd]) =>
    closing(h).by(owner(h)).everyCall((from, _, to) =>
      exists((a: Term[BigInt], b: Term[BigInt]) =>
        from < a && b <= to && threads(h).isEmpty().by(owner(h)).completed(a, Returned(True), b)))))
  .from(isEmptyReturns, closingsTraversalsReturn, setReturns, herdsAreMade, aHerdKeepsItsFields,
    currentThreadIsTheCaller)

/** The function is one closing passed to a traversal of the herd's set, before the moment. */
val traversedWith = stated { (f: Obj[Consumer[AnyRef]], h: Obj[ThreadHerd], w: Term[BigInt]) =>
  exists((from: Term[BigInt], a: Term[BigInt]) =>
    a < w && closing(h).by(owner(h)).called(from) && threads(h).forEach(f).by(owner(h)).calledInside(from, a)) }

val closingTraversesWithAFunction = Node.claim("What closing passes to a traversal of the herd's set is no null.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[AnyRef]], w: Term[BigInt]) =>
    traversedWith(f, h, w) implies (f.asValue =!= noObject)))
  .from(herdsAreMade)

val whatClosingsFunctionsApplyReturns = Node.claim(
  "The function that the functions closing passes to its traversals apply, to interrupt a thread once, returns.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[AnyRef]], x: Obj[AnyRef], c: Obj[Thread]) =>
    forall((k: Term[BigInt], g: Term[Value], t: Term[Value], a: Term[BigInt], r: Term[Response]) =>
      forall((b: Term[BigInt]) =>
        (traversedWith(f, h, k) && f.accept(x).by(c).called(k) &&
          applicationOf[Unit](g, t).by(c).calledInside(k, a) &&
          applicationOf[Unit](g, t).by(c).completed(a, r, b)) implies (r === Returned(()))))))
  .from(joinThrowsOnlyAnInterruption, interruptReturns, herdsAreMade)

// Assumed, not derived from the code. Closing keeps what interrupted it in a variable of its own, which the
// function it hands its second traversal reads and writes; the JDK's traversal applies that function on the
// thread that called it, and hands it to nothing. So only closing's caller touches the variable.
val closingKeepsItsVariableToItself = Node.assumption(
  "What a call of closing itself makes, only the thread that called closing reads, marks and writes.")(
  forall((h: Obj[ThreadHerd]) => closing(h).keepsWhatItMakesToItself)).about(About.variables)

// Assumed, not derived from the code, as the last: the two variables closing makes are held only by the functions
// it writes, so nothing else writes them.
val closingsVariablesAreWrittenByItsFunctions = Node.assumption(
  "What a call of closing itself makes is written only by a function closing has passed to a traversal, or by " +
    "a function such a function applies, itself.")(
  forall((h: Obj[ThreadHerd], from: Term[BigInt], made: Term[Value]) =>
    forall((by: Term[Value], inside: Term[Option[BigInt]], w: Term[BigInt]) =>
      (closing(h).by(owner(h)).called(from) && itselfCreates(made, owner(h).asValue, from) &&
        writesAt(made, by, inside, w)) implies
        exists((f: Obj[Consumer[AnyRef]], x: Obj[AnyRef], k: Term[BigInt]) =>
          traversedWith(f, h, k) && f.accept(x).by(owner(h)).called(k) &&
            (inside === some(k) || exists((g: Term[Value], t: Term[Value], j: Term[BigInt]) =>
              inside === some(j) && applicationOf[Unit](g, t).by(owner(h)).calledInside(k, j)))))))
    .about(About.variables)

// The second function, catching an interruption, reads closing's variable, finds it holds an exception, and
// reads it again to add to it: the second read finds what the first did, the variable being one that one thread
// alone made and writes, and that thread doing nothing between the two.
val closingsFunctionsReturn = Node.claim("A function closing passes to a traversal of the herd's set returns.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[AnyRef]], x: Obj[AnyRef], c: Obj[Thread]) =>
    forall((k: Term[BigInt], r: Term[Response], b: Term[BigInt]) =>
      (traversedWith(f, h, k) && f.accept(x).by(c).completed(k, r, b)) implies (r === Returned(())))))
  .from(whatClosingsFunctionsApplyReturns, closingKeepsItsVariableToItself, joinThrowsOnlyAnInterruption,
    addSuppressedReturns, aThreadDoesOneThingAtATime, herdsAreMade)

val closingsTraversalsReturn = Node.claim(
  "A traversal of the herd's set that closing makes itself does not throw.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[AnyRef]], from: Term[BigInt], a: Term[BigInt], b: Term[BigInt]) =>
    forall((r: Term[Response]) =>
      (closing(h).by(owner(h)).called(from) && threads(h).forEach(f).by(owner(h)).calledInside(from, a) &&
        threads(h).forEach(f).by(owner(h)).completed(a, r, b)) implies (r === Returned(())))))
  .from(aTraversalThrowsOnlyWhatItsFunctionThrew, closingTraversesWithAFunction, closingsFunctionsReturn)

// Assumed, and false of Ox 1.1.0 in a rare race that can be reproduced: nothing in its code makes it hold. A fork
// that passed startThread's check before the flag was set may add a thread while closing asks; `isEmpty` is then
// no snapshot, and may answer yes of a set that was never empty. What is proven of a closed herd's set and of
// its forks rests on it, until the patched code is what the model reads.
val nothingIsAddedDuringTheLastCheck = Node.assumption(
  "While a call closing makes asks whether the herd's set is empty and is answered yes, nothing is added to it.")(
  forall((h: Obj[ThreadHerd], a: Term[BigInt], b: Term[BigInt]) =>
    threads(h).isEmpty().by(owner(h)).completed(a, Returned(True), b) implies !addedDuring(threads(h), a, b)))
    .about(About.falseOfOx)
