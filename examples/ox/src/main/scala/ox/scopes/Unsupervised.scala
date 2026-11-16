package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.threads.*

// `unsupervised` makes a scope, with a herd of its own, runs the code it is given in it, and gives what that gives:
// so the scope's herd is closed once `unsupervised` has completed.

/** `unsupervised(locals, code)`: what `unsupervised(code)` runs. */
def unsupervisedWith(locals: Term[Value], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.unsupervised[Any](???, ???)), locals, code)

/** A call of `unsupervised` by `c` from `from` to `to`, in which it made the scope `s`. */
def unsupervisedMade(c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt])(using Stating)
    : Term[Boolean] =
  exists((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    exists((code: Term[Value], ended: Term[Response], a: Term[BigInt], b: Term[BigInt]) =>
      unsupervisedWith(locals, code).by(c).completed(from, ended, to) &&
        makingAScope(supervisor, errorMode, parent, locals).by(c).calledInside(from, a) &&
        makingAScope(supervisor, errorMode, parent, locals).by(c).completed(a, Returned(s), b)))

val unsupervisedRunsInTheScopeItMade = Node.claim(
  "A call of unsupervised that made a scope completes only after a call it made itself, running code in that " +
    "scope, has completed.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    unsupervisedMade(c, s, from, to) implies
      exists((g: Term[Value], a2: Term[BigInt], ran: Term[Response], b2: Term[BigInt]) =>
        runningIn(s, g).by(c).calledInside(from, a2) && runningIn(s, g).by(c).completed(a2, ran, b2) &&
          b2 <= to)))

val unsupervisedClosesItsScopesHerd = Node.claim(
  "Once a call of unsupervised has completed, closing the herd of the scope it made has completed.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    unsupervisedMade(c, s, from, to) implies closed(herdOf(s), to)))

val noForkRunsOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, no fork of the herd of the scope it made runs the code it was " +
    "made to run.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((t: Obj[Thread], forked: Obj[Code], w: Term[BigInt]) =>
      (unsupervisedMade(c, s, from, to) && to <= w && madeToRun(t, herdOf(s), forked, w)) implies
        (!forked().by(t).pendingAt(w) && !forked().by(t).called(w)))))

val nothingIsAddedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, no thread is added to the set of the herd of the scope it made.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((t: Obj[Thread], w: Term[BigInt]) =>
      (unsupervisedMade(c, s, from, to) && to <= w) implies !threads(herdOf(s)).add(t).called(w))))

val noThreadIsStartedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, a call of startThread of the herd of the scope it made does not " +
    "return, and adds no thread itself.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((code: Obj[Code], d: Obj[Thread], t: Obj[Thread], m: Term[BigInt], w: Term[BigInt]) =>
      (unsupervisedMade(c, s, from, to) && to <= m && starting(herdOf(s), code).by(d).called(m)) implies
        (!starting(herdOf(s), code).by(d).completed(m, Returned(()), w) &&
          !threads(herdOf(s)).add(t).by(d).calledInside(m, w)))))
