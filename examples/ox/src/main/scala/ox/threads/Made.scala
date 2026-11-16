package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.{ConcurrentHashMap, ThreadFactory}
import java.util.concurrent.atomic.AtomicBoolean
import ox.internal.ThreadHerd

// How a herd is made: what its constructor, as Ox's jar has it, gives each of its fields.

/** Making a herd with the factory: a call of its constructor. */
def makingAHerd(f: Obj[ThreadFactory])(using Stating): Call[ThreadHerd] = new ThreadHerd(f)

val herdsAreConstructed = Node.assumption(
  "A method of a herd is called only on a herd that a call of its constructor has returned.")(
  forall((h: Obj[ThreadHerd]) => h.isConstructedWhenCalled))

val aHerdHoldsWhatItWasGiven = Node.assumption("Each val of a herd holds what it was given when the herd was made.")(
  forall((h: Obj[ThreadHerd]) => h.holdsWhatItsValsAreGiven))

val herdsAreMade = Node.claim("A method of a herd is called only on a herd that has been made.")(
  forall((h: Obj[ThreadHerd]) => h.isMadeWhenCalled))

val aHerdsFlagIsNew = Node.claim(
  "What a herd holds as its flag is what `new AtomicBoolean(false)` returned to the call of the constructor " +
    "that returned the herd.")(
  forall((f: Obj[ThreadFactory], c: Obj[Thread], h: Obj[ThreadHerd], from: Term[BigInt], to: Term[BigInt]) =>
    makingAHerd(f).by(c).completed(from, Returned(h), to) implies
      exists((a: Term[BigInt], b: Term[BigInt]) => from < a && b <= to &&
        call(new AtomicBoolean(false)).by(c).calledInside(from, a) &&
        call(new AtomicBoolean(false)).by(c).completed(a, Returned(shutdown(h)), b))))

val aHerdsSetIsNew = Node.claim(
  "What a herd holds as its set is what `ConcurrentHashMap.newKeySet()` returned to the call of the constructor " +
    "that returned the herd.")(
  forall((f: Obj[ThreadFactory], c: Obj[Thread], h: Obj[ThreadHerd], from: Term[BigInt], to: Term[BigInt]) =>
    makingAHerd(f).by(c).completed(from, Returned(h), to) implies
      exists((a: Term[BigInt], b: Term[BigInt]) => from < a && b <= to &&
        ConcurrentHashMap.newKeySet[AnyRef]().by(c).calledInside(from, a) &&
        ConcurrentHashMap.newKeySet[AnyRef]().by(c).completed(a, Returned(threads(h)), b))))
