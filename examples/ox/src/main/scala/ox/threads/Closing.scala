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

// Not proven of the code: it is of the two functions closing passes to `forEach`, which interrupt each thread
// and join it, and of what `forEach`, `interrupt` and `join` throw.
val closingsTraversalsReturn = Node.claim(
  "A traversal of the herd's set that closing makes itself does not throw.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[Thread]], from: Term[BigInt], a: Term[BigInt], b: Term[BigInt]) =>
    forall((r: Term[Response]) =>
      (closing(h).by(owner(h)).called(from) && threads(h).forEach(f).by(owner(h)).calledInside(from, a) &&
        threads(h).forEach(f).by(owner(h)).completed(a, r, b)) implies (r === Returned(())))))

// Not proven, and not known to hold. A fork that passed startThread's check before the flag was set may add a
// thread while closing asks; `isEmpty` is then no snapshot, and may answer yes of a set that was never empty.
val nothingIsAddedDuringTheLastCheck = Node.claim(
  "While a call closing makes asks whether the herd's set is empty and is answered yes, nothing is added to it.")(
  forall((h: Obj[ThreadHerd], a: Term[BigInt], b: Term[BigInt]) =>
    threads(h).isEmpty().by(owner(h)).completed(a, Returned(True), b) implies !addedDuring(threads(h), a, b)))
