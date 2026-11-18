package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.{ConcurrentHashMap, ThreadFactory}
import java.util.concurrent.atomic.AtomicBoolean
import ox.OxError
import ox.internal.ThreadHerd

// The words of the model: a herd's set and its owner, and what a thread is to a herd. Every word is said of calls
// of Ox's own code and of the JDK.

/** A concurrent set of objects, as the JDK has it: what is assumed of one is assumed of any, whatever it holds. */
type ConcurrentSet = ConcurrentHashMap.KeySetView[AnyRef, java.lang.Boolean]

/** Code given to run: what `startThread` and a fork function take. */
type Code = () => Unit

/** The set a herd keeps its threads in. */
def threads(h: Obj[ThreadHerd])(using Stating): Obj[ConcurrentSet] = h.field("threads").seenAs[ConcurrentSet]
def owner(h: Obj[ThreadHerd])(using Stating): Obj[Thread] = h.field("herdOwner")

def shutdown(h: Obj[ThreadHerd])(using Stating): Obj[AtomicBoolean] = h.field("shutdownInProgress")
def factory(h: Obj[ThreadHerd])(using Stating): Obj[ThreadFactory] = h.field("threadFactory")

/** Closing a herd: interrupting its threads and waiting until none is left. */
def closing(h: Obj[ThreadHerd])(using Stating): Call[Unit] = h.interruptAllAndJoinUntilCompleted()

/** Starting a thread of the herd to run the code. */
def starting(h: Obj[ThreadHerd], code: Obj[Code])(using Stating): Call[Unit] = h.startThread(code.byName)

/** The thread is a fork of the herd: a call that adds it to the herd's set has returned. */
val forkOf = stated { (t: Obj[Thread], h: Obj[ThreadHerd], w: Moment) => threads(h).add(t).returnedBefore(w) }

/** The fork has left: a call that takes it out of the set has been made. */
val hasLeft = stated { (t: Obj[Thread], h: Obj[ThreadHerd], w: Moment) => threads(h).remove(t).calledBefore(w) }

/** The fork has not left. */
val live = stated { (t: Obj[Thread], h: Obj[ThreadHerd], w: Moment) => forkOf(t, h, w) && !hasLeft(t, h, w) }

/** The fork was made to run the code: its thread was added, by a call that has returned, during
  * `startThread(code)`, by its caller.
  */
val madeToRun = stated { (t: Obj[Thread], h: Obj[ThreadHerd], code: Obj[Code], w: Moment) =>
  exists((c: Obj[Thread], from: Moment, added: Term[Value], to: Moment) =>
    to <= w && threads(h).add(t).by(c).completed(from, make[Response.Returned](added), to) &&
      starting(h, code).by(c).pendingAt(from)) }

/** Closing the herd, by its owner, has completed: a call of it has, by the moment. */
val closed = stated { (h: Obj[ThreadHerd], w: Moment) =>
  exists((from: Moment, ended: Term[Response], to: Moment) =>
    to <= w && closing(h).by(owner(h)).completed(from, ended, to)) }

/** From the moment on, no fork of the herd runs the code it was made to run. */
val noForkRunsFrom = stated { (h: Obj[ThreadHerd], from: Moment) =>
  forall((t: Obj[Thread], forked: Obj[Code], w: Moment) =>
    (from <= w && madeToRun(t, h, forked, w)) implies
      (!forked().by(t).pendingAt(w) && !forked().by(t).called(w))) }

/** From the moment on, no thread is added to the herd's set. */
val nothingIsAddedFrom = stated { (h: Obj[ThreadHerd], from: Moment) =>
  forall((t: Obj[Thread], w: Moment) => from <= w implies !threads(h).add(t).called(w)) }

/** A call of the herd's startThread made from the moment on does not return, and adds no thread itself. */
val refusesToStartFrom = stated { (h: Obj[ThreadHerd], from: Moment) =>
  forall((code: Obj[Code], d: Obj[Thread], t: Obj[Thread], m: Moment, w: Moment) =>
    (from <= m && starting(h, code).by(d).called(m)) implies
      (!starting(h, code).by(d).completed(m, Returned(()), w) &&
        !threads(h).add(t).by(d).calledInside(m, w))) }

/** The thread is inside the herd's scope: its owner before it calls closing, or a fork of it that has not left. */
val inside = stated { (c: Obj[Thread], h: Obj[ThreadHerd], w: Moment) =>
  (c === owner(h) && !closing(h).by(owner(h)).calledBefore(w)) || live(c, h, w) }

/** Nothing is in the herd's set. */
val empty = stated { (h: Obj[ThreadHerd], w: Moment) =>
  forall((y: Term[Value]) => !elements(threads(h), w).contains(y)) }

/** A thread running the function: `r.run()`. A term's own `run` hides the method, so the call is made of the
  * method's name, taken from the code.
  */
def running(r: Obj[Runnable]): Call[Unit] = Call.of[Unit](methodOf[Runnable](_.run()), r.asValue)

/** The function was handed to the herd's factory, by a call of startThread on the herd itself, before the
  * moment: it is what a thread of the herd runs.
  */
val handedOver = stated { (r: Obj[Runnable], h: Obj[ThreadHerd], w: Moment) =>
  exists((code: Obj[Code], c: Obj[Thread], from: Moment, m: Moment) =>
    m < w && starting(h, code).by(c).called(from) && factory(h).newThread(r).by(c).calledInside(from, m)) }

/** The thread was made by a thread factory, for the call of startThread made at `from` by `c` itself, by the
  * moment `b`.
  */
val madeFor = stated { (t: Obj[Thread], c: Obj[Thread], from: Moment, b: Moment) =>
  exists((f: Obj[ThreadFactory], r: Obj[Runnable], a: Moment, done: Moment) =>
    done <= b && f.newThread(r).by(c).calledInside(from, a) &&
      f.newThread(r).by(c).completed(a, Returned(t), done)) }

/** A scope, as `unsupervised` and `supervised` make it. */
type Scope = OxError[Nothing, [T] =>> T]

/** The herd a scope holds. */
def herdOf(s: Obj[Scope])(using Stating): Obj[ThreadHerd] = s.field("herd")

/** Making a scope: `OxError(supervisor, errorMode, parent, locals)`, which makes the scope's herd. */
def makingAScope(supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value])
    : Call[Scope] =
  Call.of[Scope](methodCalled(OxError[Nothing, [T] =>> T](???, ???, ???, ???)), supervisor, errorMode, parent,
    locals)

/** The herd is ready by the moment: a call of its constructor has returned it, or a call making a scope has
  * returned a scope that holds it. These are the two ways the code read makes a herd: where Ox's own code makes
  * one, for a scope, it makes it in place, and no call of the constructor is an event.
  */
val ready = stated { (h: Obj[ThreadHerd], w: Moment) =>
  h.isConstructed(w) ||
    exists((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
      exists((s: Obj[Scope], from: Moment, to: Moment) =>
        to <= w && makingAScope(supervisor, errorMode, parent, locals).completed(from, Returned(s), to) &&
          (herdOf(s) === h))) }
