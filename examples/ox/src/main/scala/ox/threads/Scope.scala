package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.{OxError, OxUnsupervised}
import ox.internal.ThreadHerd

// A scope of Ox. `unsupervised` makes one, with a herd of its own, runs the code it is given in it, and closes the
// herd before it ends: so what holds of a closed herd holds of the scope's herd once `unsupervised` has completed.

/** A scope, as `unsupervised` makes it. */
type Scope = OxError[Nothing, [T] =>> T]

/** The herd a scope holds. */
def herdOf(s: Obj[Scope])(using Stating): Obj[ThreadHerd] = s.field("herd")

/** Making a scope: `OxError(supervisor, errorMode, parent, locals)`, which makes the scope's herd. */
def makingAScope(supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value])
    : Call[Scope] =
  Call.of[Scope](methodCalled(OxError[Nothing, [T] =>> T](???, ???, ???, ???)), supervisor, errorMode, parent,
    locals)

/** Running code in a scope until the scope ends: `scopedWithCapability(scope)(code)`. */
def runningIn(s: Obj[Scope], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.scopedWithCapability[Any](???)(???)), s.asValue, code)

/** `unsupervised(locals, code)`: what `unsupervised(code)` runs. */
def unsupervisedWith(locals: Term[Value], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.unsupervised[Any](???, ???)), locals, code)

/** Making a scope of a herd and the rest of what it holds: the `apply` the compiler writes for a case class. */
def makingAScopeOf(herd: Obj[ThreadHerd], rest: Term[Value]*): Call[Scope] =
  Call.of[Scope](methodCalled(OxError[Nothing, [T] =>> T](???, ???, ???, ???, ???, ???)), (herd.asValue +: rest)*)

// Of Scala: the `apply` of a case class is written by the compiler, and is in no tree read. It makes an object
// whose vals hold what it is given.
val aScopeHoldsTheHerdItIsMadeWith = Node.assumption("A scope made with a herd holds that herd.")(
  forall((h: Obj[ThreadHerd], finalizers: Term[Value], supervisor: Term[Value], errorMode: Term[Value]) =>
    forall((parent: Term[Value], locals: Term[Value], s: Obj[Scope]) =>
      makingAScopeOf(h, finalizers, supervisor, errorMode, parent, locals).everyCall((_, reply, _) =>
        (reply === Returned(s)) implies (herdOf(s) === h)))))

// Of Scala: `herd` is a val of a scope, asked for through the trait it is declared in.
val aScopeGivesTheHerdItHolds = Node.assumption("A scope asked for its herd gives the herd it holds.")(
  forall((s: Obj[Scope]) =>
    s.seenAs[OxUnsupervised].herd.everyCall((_, reply, _) => reply === Returned(herdOf(s)))))

// Of the JDK: a thread's current scope is kept in a `ThreadLocal`.
val theCurrentScopeIsReadAndSet = Node.assumption("Reading a thread's current scope, and setting it, return.")(
  forall((s: Obj[OxUnsupervised]) =>
    ox.internal.currentScope.get().everyCall((_, reply, _) => exists((x: Term[Value]) =>
      reply === make[Response.Returned](x))) &&
      ox.internal.currentScope.set(s).everyCall((_, reply, _) => reply === Returned(()))))

val aScopesHerdIsItsMakers = Node.claim(
  "The herd a scope holds is one whose owner is the thread that made the scope.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
      makingAScope(supervisor, errorMode, parent, locals).by(c).completed(from, Returned(s), to) implies
        (owner(herdOf(s)) === c))))

val aScopeEndsAfterItsHerdIsClosed = Node.claim(
  "Running code in a scope completes only after a call it made, closing the scope's herd, has completed.")(
  forall((s: Obj[Scope], code: Term[Value], c: Obj[Thread]) =>
    forall((from: Term[BigInt], ended: Term[Response], to: Term[BigInt]) =>
      runningIn(s, code).by(c).completed(from, ended, to) implies
        exists((a: Term[BigInt], closed: Term[Response], b: Term[BigInt]) =>
          from < a && b <= to && closing(herdOf(s)).by(c).completed(a, closed, b)))))

val unsupervisedRunsInTheScopeItMade = Node.claim(
  "A call of unsupervised that made a scope completes only after a call it made itself, running code in that " +
    "scope, has completed.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((code: Term[Value], c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], ended: Term[Response]) =>
      forall((to: Term[BigInt], a: Term[BigInt], b: Term[BigInt]) =>
        (unsupervisedWith(locals, code).by(c).completed(from, ended, to) &&
          makingAScope(supervisor, errorMode, parent, locals).by(c).calledInside(from, a) &&
          makingAScope(supervisor, errorMode, parent, locals).by(c).completed(a, Returned(s), b)) implies
          exists((g: Term[Value], a2: Term[BigInt], ran: Term[Response], b2: Term[BigInt]) =>
            runningIn(s, g).by(c).calledInside(from, a2) && runningIn(s, g).by(c).completed(a2, ran, b2) &&
              b2 <= to)))))

val noForkRunsOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, no fork of the herd of the scope it made runs the code it was " +
    "made to run.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((code: Term[Value], c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], ended: Term[Response]) =>
      forall((to: Term[BigInt], a: Term[BigInt], b: Term[BigInt]) =>
        forall((t: Obj[Thread], forked: Obj[Code], w: Term[BigInt]) =>
          (unsupervisedWith(locals, code).by(c).completed(from, ended, to) &&
            makingAScope(supervisor, errorMode, parent, locals).by(c).calledInside(from, a) &&
            makingAScope(supervisor, errorMode, parent, locals).by(c).completed(a, Returned(s), b) &&
            to <= w && madeToRun(t, herdOf(s), forked, w)) implies
            (!forked().by(t).pendingAt(w) && !forked().by(t).called(w)))))))
