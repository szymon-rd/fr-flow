package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.function.Consumer
import ox.internal.ThreadHerd
import ox.threads.*

// What closing does in time: it interrupts each thread it finds in the herd's set, and joins it.

val whatClosingsFunctionsApplyInterrupts = Node.claim(
  "Once the function that closing's functions apply to a thread has completed, the thread has been interrupted.")(
  forall((h: Obj[ThreadHerd], f: Obj[Consumer[AnyRef]], x: Obj[AnyRef], c: Obj[Thread]) =>
    forall((k: Term[BigInt], g: Term[Value], t: Obj[Thread], a: Term[BigInt], r: Term[Response]) =>
      forall((b: Term[BigInt]) =>
        (traversedWith(f, h, k) && f.accept(x).by(c).called(k) &&
          applicationOf[Unit](g, t.asValue).by(c).calledInside(k, a) &&
          applicationOf[Unit](g, t.asValue).by(c).completed(a, r, b)) implies
          t.interrupt().returnedBefore(b)))))
