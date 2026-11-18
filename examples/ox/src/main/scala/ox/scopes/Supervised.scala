package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.executions.*
import frflow.values.*
import ox.threads.*

// `supervised` makes a supervisor and a scope, with a herd of its own, and runs in the scope code that forks the
// code it is given and waits for the supervisor: so the scope's herd is closed once `supervised` has completed.

/** `supervisedError(errorMode, locals)(code)`: what `supervised(code)` and `supervisedError` run. */
def supervisedWith(errorMode: Term[Value], locals: Term[Value], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.supervisedError[Any, [T] =>> T, Any](???, ???)(???)), errorMode, locals, code)

/** A call of `supervised` by `c` from `from` to `to`, in which it made the scope `s`. */
def supervisedMade(c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment)(using Stating)
    : Term[Boolean] =
  exists((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    exists((code: Term[Value], ended: Term[Response], a: Moment, b: Moment) =>
      supervisedWith(errorMode, locals, code).by(c).completed(from, ended, to) &&
        makingAScope(supervisor, errorMode, parent, locals).by(c).calledInside(from, a) &&
        makingAScope(supervisor, errorMode, parent, locals).by(c).completed(a, Returned(s), b)))

/** Of every scope a completed call of supervised made, with the moment the call completed. */
def onceSupervisedEnds(holds: (Obj[Scope], Moment) => Term[Boolean])(using Stating): Term[Boolean] =
  forall((c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment) =>
    supervisedMade(c, s, from, to) implies holds(s, to))

val supervisedRunsInTheScopeItMade = Node.claim(
  "A call of supervised that made a scope completes only after a call it made itself, running code in that " +
    "scope, has completed.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment) =>
    supervisedMade(c, s, from, to) implies
      exists((g: Term[Value], a2: Moment, ran: Term[Response], b2: Moment) =>
        runningIn(s, g).by(c).calledInside(from, a2) && runningIn(s, g).by(c).completed(a2, ran, b2) &&
          b2 <= to)))

val supervisedClosesItsScopesHerd = Node.claim(
  "Once a call of supervised has completed, closing the herd of the scope it made has completed.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment) =>
    supervisedMade(c, s, from, to) implies closed(herdOf(s), to)))
  .from(supervisedRunsInTheScopeItMade, aScopeEndsAfterItsHerdIsClosed, aScopesHerdIsItsMakers)

val noForkRunsOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, no fork of the herd of the scope it made runs the code it was " +
    "made to run.")(
  onceSupervisedEnds((s, to) => noForkRunsFrom(herdOf(s), to)))
  .from(supervisedClosesItsScopesHerd, noForkRunsOnceClosed)

val nothingIsAddedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, no thread is added to the set of the herd of the scope it made.")(
  onceSupervisedEnds((s, to) => nothingIsAddedFrom(herdOf(s), to)))
  .from(supervisedClosesItsScopesHerd, nothingIsAddedOnceClosed)

val noThreadIsStartedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, a call of startThread of the herd of the scope it made does not " +
    "return, and adds no thread itself.")(
  onceSupervisedEnds((s, to) => refusesToStartFrom(herdOf(s), to)))
  .from(supervisedClosesItsScopesHerd, aClosedHerdRefusesToStart)
