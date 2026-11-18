package ox.live

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ThreadFactory
import ox.internal.ThreadHerd
import ox.threads.*

// What a fork does in time: `startThread` starts the thread it added; the thread runs the function it was made
// for, which runs the code, takes the thread out of the herd's set, and ends.

val startThreadAddsOnce = Node.claim("A call of startThread itself makes at most one call that adds to a set.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], from: Moment) =>
    forall((s: Obj[ConcurrentSet], t: Obj[Thread], a: Moment) =>
      forall((s2: Obj[ConcurrentSet], t2: Obj[Thread], a2: Moment) =>
        (starting(h, code).by(c).called(from) && s.add(t).by(c).calledInside(from, a) &&
          s2.add(t2).by(c).calledInside(from, a2)) implies (a === a2)))))
  .from(herdsAreMade)

val startThreadStartsWhatItAdded = Node.claim(
  "A call of startThread that has itself added a thread to the herd's set calls start on that thread, in time.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Moment, a: Moment, added: Term[Value], b: Moment) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, a) &&
        threads(h).add(t).by(c).completed(a, make[Response.Returned](added), b)) implies
        exists((m: Moment) => t.start().by(c).calledInside(from, m)))))
  .from(startThreadAddsOnce, aHerdsMethodsProceed, herdsAreMade)

val startThreadStartsAfterItsAddIsOver = Node.claim(
  "A call of startThread itself starts a thread only once each call it itself made to add to the herd's set is " +
    "over.")(
  forall((h: Obj[ThreadHerd], code: Obj[Code], c: Obj[Thread], t: Obj[Thread]) =>
    forall((from: Moment, w: Moment, m: Moment, started: Obj[Thread]) =>
      (starting(h, code).by(c).called(from) && threads(h).add(t).by(c).calledInside(from, w) &&
        started.start().by(c).calledInside(from, m)) implies !threads(h).add(t).by(c).pendingSince(w, m))))
  .from(herdsAreMade)

val aForkFunctionRemovesItsThread = Node.claim(
  "A call of a function startThread handed a thread factory that has completed has asked for the current " +
    "thread and then removed it from the herd's set, by a call that is over.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], code: Obj[Code], t: Obj[Thread]) =>
    forall((i: Moment, ended: Term[Response], e: Moment) =>
      (forkFunction(r, h, code) && running(r).by(t).completed(i, ended, e)) implies
        exists((a: Moment, b: Moment) =>
          Thread.currentThread().by(t).completed(a, Returned(t), b) &&
            threads(h).remove(t).by(t).completedWithin(b, e)))))
  .from(herdsAreMade, aHerdKeepsItsFields, currentThreadIsTheCaller)

val aForkFunctionCompletesOnceItsCodeDoes = Node.claim(
  "A call of a function startThread handed a thread factory is responded to in time, if each call it itself " +
    "makes of the code startThread was given is.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], code: Obj[Code], t: Obj[Thread], i: Moment) =>
    (forkFunction(r, h, code) && running(r).by(t).called(i) &&
      forall((m: Moment) => code().by(t).calledInside(i, m) implies code().by(t).respondedTo(m))) implies
      running(r).by(t).respondedTo(i)))
  .from(aForkFunctionProceeds, currentThreadResponds, removingResponds, discardResponds, herdsAreMade)

val aForkEndsOnceInterrupted = Node.claim(
  "A thread added to a herd's set runs, to its end and in time, the function a factory made it for, once it " +
    "has been interrupted.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread], code: Obj[Code], made: Moment) =>
    (madeToRun(t, h, code, made) && interrupted(t)) implies
      exists((f: Obj[ThreadFactory], r: Obj[Runnable], a: Moment, b: Moment, i: Moment) =>
        f.newThread(r).completed(a, Returned(t), b) && running(r).by(t).respondedTo(i))))
  .from(startThreadStartsWhatItAdded, aStartedThreadRunsItsFunction, aForkFunctionCompletesOnceItsCodeDoes,
    forkCodeCompletesOnceInterrupted, onlyStartThreadAddsToTheSet, startThreadAddsWhileItRuns,
    startThreadAddsWhatItsFactoryMade, herdsAreConstructed)
