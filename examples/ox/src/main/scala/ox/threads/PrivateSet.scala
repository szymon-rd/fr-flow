package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ConcurrentHashMap
import java.util.function.Consumer
import ox.internal.ThreadHerd

// What a herd keeps to itself: its set. As of its flag, that nothing but the herd's own code calls anything on it
// is assumed, and said to be. Its own code is its methods and the functions startThread hands the factory; what
// each calls is proven of its tree, and with that who adds to the set and who removes from it.

/** The thread begins to run, at the moment, a function that startThread handed the herd's factory. */
def aForkFunctionRuns(h: Obj[ThreadHerd], by: Term[Value], i: Moment)(using Stating): Term[Boolean] =
  exists((r: Obj[Runnable]) => handedOver(r, h, i) && running(r).by(Ref.of[Thread](by)).called(i))

/** The invocation is of a method a key set can be called by. */
def ofAKeySet(made: Term[Invocation]): Term[Boolean] =
  exists((method: Term[String], taking: Term[List[Value]]) =>
    made === make[Invocation](method, taking) && methodsOf[ConcurrentSet].map(method === _).reduce(_ || _))

// Assumed, not derived from the code. The set is a private val, made in the herd's constructor; the herd's
// methods and the functions written in them are the only code that names it, and they hand it to nothing.
val aHerdKeepsItsSetToItself = Node.assumption(
  "What a herd holds as its set is called on only by the herd's own methods and by the functions startThread " +
    "handed its factory, themselves.")(
  forall((h: Obj[ThreadHerd], w: Moment) =>
    ready(h, w) implies h.keepsToItself(threads(h).asValue)((by, i) => aForkFunctionRuns(h, by, i))))
    .about(About.privateField)

val aKeySetHasOnlyItsMethods = Node.assumption(
  "On what `ConcurrentHashMap.newKeySet` returned, only methods of a key set are called.")(
  forall((s: Obj[ConcurrentSet], from: Moment, to: Moment) =>
    ConcurrentHashMap.newKeySet[AnyRef]().completed(from, Returned(s), to) implies
      forall((method: Term[String], w: Moment) =>
        calledOn(s.asValue, method, w) implies methodsOf[ConcurrentSet].map(method === _).reduce(_ || _))))
    .about(About.jdk)

val theForkFunctionCallsFour = Node.claim(
  "The function startThread hands the factory itself calls only the code, Thread.currentThread, remove of a " +
    "set, and Ox's discard.")(
  forall((h: Obj[ThreadHerd], r: Obj[Runnable], c: Obj[Thread]) =>
    forall((i: Moment, made: Term[Invocation], w: Moment) =>
      (handedOver(r, h, i) && running(r).by(c).called(i) && itselfMakes(made, c.asValue, i, w)) implies
        (exists((code: Obj[Code]) => code().isCall(made)) || Thread.currentThread().isCall(made) ||
          exists((s: Obj[ConcurrentSet], t: Obj[Thread]) => s.remove(t).isCall(made)) ||
          exists((x: Obj[AnyRef]) => ox.discard(x).isCall(made))))))
  .from(herdsAreMade)

val whatAHerdsCodeCallsOfASet = Node.claim(
  "Of the methods of a key set, startThread itself calls only add, closing isEmpty and forEach, the membership " +
    "check contains, and a function startThread handed the factory remove.")(
  forall((h: Obj[ThreadHerd], c: Obj[Thread], i: Moment, made: Term[Invocation], w: Moment) =>
    ((h.isCalledBy(c.asValue, i) || aForkFunctionRuns(h, c.asValue, i)) && itselfMakes(made, c.asValue, i, w) &&
      ofAKeySet(made)) implies
      ((exists((code: Obj[Code]) => starting(h, code).by(c).called(i)) &&
        exists((s: Obj[ConcurrentSet], t: Obj[Thread]) => s.add(t).isCall(made))) ||
        (closing(h).by(c).called(i) && (exists((s: Obj[ConcurrentSet]) => s.isEmpty().isCall(made)) ||
          exists((s: Obj[ConcurrentSet], f: Obj[Consumer[AnyRef]]) => s.forEach(f).isCall(made)))) ||
        (exists((t: Obj[Thread]) => h.isOwnerOrHerdThread(t).by(c).called(i)) &&
          exists((s: Obj[ConcurrentSet], x: Obj[AnyRef]) => s.contains(x).isCall(made))) ||
        (aForkFunctionRuns(h, c.asValue, i) &&
          exists((s: Obj[ConcurrentSet], t: Obj[Thread]) => s.remove(t).isCall(made))))))
  .from(closingCallsFour, theOwnerCheckCallsCurrentThread, theMembershipCheckCallsContains, theForkFunctionCallsFour,
    startThreadCallsFive, theClosingCheckCallsGet, theTreeCheckCallsFour)
