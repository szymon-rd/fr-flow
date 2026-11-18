package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicBoolean
import ox.internal.ThreadHerd

// How a herd is made: what its constructor, as Ox's jar has it, gives each of its fields.

// A herd does not leave what makes it before it is made: its constructor hands it to nothing, and the scope's
// `apply`, which makes one in place, only to the scope it returns.
val herdsAreConstructed = Node.assumption(
  "A method of a herd is called only on a herd that is ready: one that a call of its constructor has " +
    "returned, or that a scope returned by a call making a scope holds.")(
  forall((h: Obj[ThreadHerd]) => h.whenCalled(w => ready(h, w)))).about(About.objects)

val aHerdHoldsWhatItWasGiven = Node.assumption("Each val of a herd holds what it was given when the herd was made.")(
  forall((h: Obj[ThreadHerd]) => h.holdsWhatItsValsAreGiven)).about(About.objects)

val herdsAreMade = Node.claim("A method of a herd is called only on a herd that has been made.")(
  forall((h: Obj[ThreadHerd]) => h.isMadeWhenCalled))

val aHerdsFlagIsNew = Node.claim(
  "What a ready herd holds as its flag is what a call of `new AtomicBoolean(false)` returned.")(
  forall((h: Obj[ThreadHerd], w: Term[BigInt]) =>
    ready(h, w) implies exists((a: Term[BigInt], b: Term[BigInt]) =>
      call(new AtomicBoolean(false)).completed(a, Returned(shutdown(h)), b))))

val aHerdsSetIsNew = Node.claim(
  "What a ready herd holds as its set is what a call of `ConcurrentHashMap.newKeySet()` returned.")(
  forall((h: Obj[ThreadHerd], w: Term[BigInt]) =>
    ready(h, w) implies exists((a: Term[BigInt], b: Term[BigInt]) =>
      ConcurrentHashMap.newKeySet[AnyRef]().completed(a, Returned(threads(h)), b))))
