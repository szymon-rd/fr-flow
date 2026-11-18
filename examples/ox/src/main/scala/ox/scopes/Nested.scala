package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.internal.ThreadHerd
import ox.threads.*

// A thread's calls nest: what a thread begins while a call of its own is pending is over before that call is. So
// what a fork of a scope began while running its code is over once the scope's call has completed: a scope
// opened there has ended.

// Of the JVM: a call returns to the call that made it, and so only once each call made in it has returned.
val aCallEndsAfterTheCallsItMade = Node.assumption(
  "A call is responded to only once each call it made itself is over.")(
  forall((by: Term[Value], from: Moment, a: Term[Response], spawns: Term[List[Spawn]]) =>
    forall((k: Moment, inner: Term[Invocation], m: Moment) =>
      (history(k) === make[Event.Respond](by, from, a, spawns) && m < k &&
        history(m) === make[Event.Invoke](by, some(from), inner)) implies overBy(by, m, k)))).about(About.jdk)

val callsNest = Node.claim(
  "A call that a thread begins while a call of its own is pending is over before that call is.")(
  forall((by: Obj[Thread], outer: Term[Invocation], from: Moment, inner: Term[Invocation]) =>
    forall((m: Moment, e: Moment) =>
      (begun(outer, by.asValue, from) && from < m && !overBy(by.asValue, from, m) &&
        begun(inner, by.asValue, m) && overBy(by.asValue, from, e)) implies overBy(by.asValue, m, e))))
  .from(aCallEndsAfterTheCallsItMade, aThreadDoesOneThingAtATime)

/** Each call that a fork of the herd began while running the code it was made to run is over by the moment. */
val whatForksBeganIsOverBy = stated { (h: Obj[ThreadHerd], by: Moment) =>
  forall((t: Obj[Thread], forked: Obj[Code], inner: Term[Invocation], m: Moment) =>
    (madeToRun(t, h, forked, m) && forked().by(t).pendingAt(m) && begun(inner, t.asValue, m)) implies
      overBy(t.asValue, m, by)) }

val whatAForkBeganIsOverOnceClosed = Node.claim(
  "After closing a herd has completed, each call that a fork of it began while running the code it was made " +
    "to run is over.")(
  forall((h: Obj[ThreadHerd], by: Moment) => closed(h, by) implies whatForksBeganIsOverBy(h, by)))
  .from(noForkRunsOnceClosed, callsNest)

val whatAForkBeganIsOverOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, each call that a fork of the scope it made began while running " +
    "the code it was made to run is over.")(
  onceUnsupervisedEnds((s, to) => whatForksBeganIsOverBy(herdOf(s), to)))
  .from(unsupervisedClosesItsScopesHerd, whatAForkBeganIsOverOnceClosed)

val whatAForkBeganIsOverOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, each call that a fork of the scope it made began while running " +
    "the code it was made to run is over.")(
  onceSupervisedEnds((s, to) => whatForksBeganIsOverBy(herdOf(s), to)))
  .from(supervisedClosesItsScopesHerd, whatAForkBeganIsOverOnceClosed)
