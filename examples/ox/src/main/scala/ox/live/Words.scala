package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import ox.internal.ThreadHerd
import ox.threads.*

// The words of what happens in time.

/** The function is one a call of `startThread(code)` on the herd itself handed a thread factory. */
val forkFunction = stated { (r: Obj[Runnable], h: Obj[ThreadHerd], code: Obj[Code]) =>
  exists((c: Obj[Thread], from: Term[BigInt], f: Obj[ThreadFactory], m: Term[BigInt]) =>
    starting(h, code).by(c).called(from) && f.newThread(r).by(c).calledInside(from, m)) }

/** The thread has been interrupted: a call of `interrupt` on it has returned. */
val interrupted = stated { (t: Obj[Thread]) => exists((w: Term[BigInt]) => t.interrupt().returnedBefore(w)) }
