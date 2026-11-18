package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.executions.*
import frflow.values.*
import ox.threads.*

// A fork is started by calling `startThread` on the herd of its scope: so starting a fork in a scope whose herd
// is closed does not return. Of `forkUnsupervised` and of `forkCancellable`, read from Ox's code.

/** Starting a fork of the code in the scope, unsupervised: `forkUnsupervised(code)(using s)`. */
def forkingUnsupervised(code: Term[Value], s: Obj[Scope]): Call[Any] =
  Call.of[Any](methodCalled(ox.forkUnsupervised[Any](???)(using ???)), code, s.asValue)

/** A call of the fork method in the scope, made from the moment on, does not return a fork. */
def refusesFrom(call: (Term[Value], Obj[Scope]) => Call[Any])(s: Obj[Scope], from: Moment)(using Stating)
    : Term[Boolean] =
  forall((code: Term[Value], d: Obj[Thread], m: Moment, fork: Term[Value], w: Moment) =>
    (from <= m && call(code, s).by(d).called(m)) implies !call(code, s).by(d).completed(m, Returned(fork), w))

val forkUnsupervisedStartsAThread = Node.claim(
  "A call of forkUnsupervised returns only after a call of startThread on the herd of its scope, that it made " +
    "itself, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Moment, fork: Term[Value], to: Moment) =>
      forkingUnsupervised(code, s).by(c).completed(from, make[Response.Returned](fork), to) implies
        exists((run: Obj[Code], a: Moment, b: Moment) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).calledInside(from, a) &&
            starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))
  .from(aScopeGivesTheHerdItHolds)

val forkUnsupervisedIsRefusedOnceClosed = Node.claim(
  "After closing a herd has completed, a call of forkUnsupervised in a scope that holds the herd does not " +
    "return.")(
  forall((s: Obj[Scope], from: Moment) => closed(herdOf(s), from) implies refusesFrom(forkingUnsupervised)(s, from)))
  .from(forkUnsupervisedStartsAThread, aClosedHerdRefusesToStart)

val forkUnsupervisedIsRefusedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, a call of forkUnsupervised in the scope it made does not return.")(
  onceUnsupervisedEnds(refusesFrom(forkingUnsupervised)))
  .from(unsupervisedClosesItsScopesHerd, forkUnsupervisedIsRefusedOnceClosed)

val forkUnsupervisedIsRefusedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, a call of forkUnsupervised in the scope it made does not return.")(
  onceSupervisedEnds(refusesFrom(forkingUnsupervised)))
  .from(supervisedClosesItsScopesHerd, forkUnsupervisedIsRefusedOnceClosed)

/** Starting a fork of the code in the scope, that can be cancelled: `forkCancellable(code)(using s)`. */
def forkingCancellable(code: Term[Value], s: Obj[Scope]): Call[Any] =
  Call.of[Any](methodCalled(ox.forkCancellable[Any](???)(using ???)), code, s.asValue)

val forkCancellableStartsAThread = Node.claim(
  "A call of forkCancellable returns only after a call of startThread on the herd of its scope, that it made " +
    "itself, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Moment, fork: Term[Value], to: Moment) =>
      forkingCancellable(code, s).by(c).completed(from, make[Response.Returned](fork), to) implies
        exists((run: Obj[Code], a: Moment, b: Moment) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).calledInside(from, a) &&
            starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))
  .from(aScopeGivesTheHerdItHolds)

val forkCancellableIsRefusedOnceClosed = Node.claim(
  "After closing a herd has completed, a call of forkCancellable in a scope that holds the herd does not " +
    "return.")(
  forall((s: Obj[Scope], from: Moment) => closed(herdOf(s), from) implies refusesFrom(forkingCancellable)(s, from)))
  .from(forkCancellableStartsAThread, aClosedHerdRefusesToStart)

val forkCancellableIsRefusedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, a call of forkCancellable in the scope it made does not return.")(
  onceUnsupervisedEnds(refusesFrom(forkingCancellable)))
  .from(unsupervisedClosesItsScopesHerd, forkCancellableIsRefusedOnceClosed)

val forkCancellableIsRefusedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, a call of forkCancellable in the scope it made does not return.")(
  onceSupervisedEnds(refusesFrom(forkingCancellable)))
  .from(supervisedClosesItsScopesHerd, forkCancellableIsRefusedOnceClosed)
