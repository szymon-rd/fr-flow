package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.executions.*
import frflow.values.*
import ox.threads.*

// `unsupervised` makes a scope, with a herd of its own, runs the code it is given in it, and gives what that gives:
// so the scope's herd is closed once `unsupervised` has completed.

/** `unsupervised(locals, code)`: what `unsupervised(code)` runs. */
def unsupervisedWith(locals: Term[Value], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.unsupervised[Any](???, ???)), locals, code)

/** A call of `unsupervised` by `c` from `from` to `to`, in which it made the scope `s`. */
def unsupervisedMade(c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment)(using Stating)
    : Term[Boolean] =
  exists((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    exists((code: Term[Value], ended: Term[Response], a: Moment, b: Moment) =>
      unsupervisedWith(locals, code).by(c).completed(from, ended, to) &&
        makingAScope(supervisor, errorMode, parent, locals).by(c).calledInside(from, a) &&
        makingAScope(supervisor, errorMode, parent, locals).by(c).completed(a, Returned(s), b)))

/** Of every scope a completed call of unsupervised made, with the moment the call completed. */
def onceUnsupervisedEnds(holds: (Obj[Scope], Moment) => Term[Boolean])(using Stating): Term[Boolean] =
  forall((c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment) =>
    unsupervisedMade(c, s, from, to) implies holds(s, to))

val unsupervisedRunsInTheScopeItMade = Node.claim(
  "A call of unsupervised that made a scope completes only after a call it made itself, running code in that " +
    "scope, has completed.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment) =>
    unsupervisedMade(c, s, from, to) implies
      exists((g: Term[Value], a2: Moment, ran: Term[Response], b2: Moment) =>
        runningIn(s, g).by(c).calledInside(from, a2) && runningIn(s, g).by(c).completed(a2, ran, b2) &&
          b2 <= to)))

val unsupervisedClosesItsScopesHerd = Node.claim(
  "Once a call of unsupervised has completed, closing the herd of the scope it made has completed.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment) =>
    unsupervisedMade(c, s, from, to) implies closed(herdOf(s), to)))
  .from(unsupervisedRunsInTheScopeItMade, aScopeEndsAfterItsHerdIsClosed, aScopesHerdIsItsMakers)

val noForkRunsOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, no fork of the herd of the scope it made runs the code it was " +
    "made to run.")(
  onceUnsupervisedEnds((s, to) => noForkRunsFrom(herdOf(s), to)))
  .from(unsupervisedClosesItsScopesHerd, noForkRunsOnceClosed)

val nothingIsAddedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, no thread is added to the set of the herd of the scope it made.")(
  onceUnsupervisedEnds((s, to) => nothingIsAddedFrom(herdOf(s), to)))
  .from(unsupervisedClosesItsScopesHerd, nothingIsAddedOnceClosed)

val noThreadIsStartedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, a call of startThread of the herd of the scope it made does not " +
    "return, and adds no thread itself.")(
  onceUnsupervisedEnds((s, to) => refusesToStartFrom(herdOf(s), to)))
  .from(unsupervisedClosesItsScopesHerd, aClosedHerdRefusesToStart)
