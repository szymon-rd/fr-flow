package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.atomic.AtomicBoolean
import java.util.function.Consumer
import ox.internal.ThreadHerd

// What a herd keeps to itself. That nothing but the herd's own methods calls anything on its flag is assumed, and
// said to be: it is not derived from the code. What each of those methods calls is proven of its tree, and with
// that what is called on the flag, and by what.

/** The herd's check that its caller is its owner, which only its own code may name. */
def ownerCheck(h: Obj[ThreadHerd]): Call[Unit] = h.method[Unit]("assertOnOwnerThread")

/** The invocation is of a method an atomic boolean can be called by. */
def ofAnAtomicBoolean(made: Term[Invocation]): Term[Boolean] =
  exists((method: Term[String], taking: Term[List[Value]]) =>
    made === make[Invocation](method, taking) && methodsOf[AtomicBoolean].map(method === _).reduce(_ || _))

// Assumed, not derived from the code. The flag is a private val, made in the herd's constructor and given to
// nothing: that then only the herd's methods reach it is what the JVM and Scala make of a private field, with no
// reflection. No rule here says so of a private field in general.
val aHerdKeepsItsFlagToItself = Node.assumption(
  "What a herd holds as its flag is called on only by the herd's own methods, themselves.")(
  forall((h: Obj[ThreadHerd], w: Term[BigInt]) =>
    ready(h, w) implies h.keepsToItself(shutdown(h).asValue)((_, _) => False)))

val anAtomicBooleanHasOnlyItsMethods = Node.assumption(
  "On what `new AtomicBoolean` returned, only methods of an atomic boolean are called.")(
  forall((b: Obj[AtomicBoolean], x: Term[Boolean], from: Term[BigInt], to: Term[BigInt]) =>
    call(new AtomicBoolean(x)).completed(from, Returned(b), to) implies
      forall((method: Term[String], w: Term[BigInt]) =>
        calledOn(b.asValue, method, w) implies methodsOf[AtomicBoolean].map(method === _).reduce(_ || _))))

val closingCallsFour = Node.claim(
  "A call of closing itself calls only the herd's check of its owner, set of an atomic flag to true, and " +
    "isEmpty and forEach of a set.")(
  forall((h: Obj[ThreadHerd]) =>
    closing(h).itselfCallsOnly(made =>
      ownerCheck(h).isCall(made) || exists((b: Obj[AtomicBoolean]) => b.set(true).isCall(made)) ||
        exists((s: Obj[ConcurrentSet]) => s.isEmpty().isCall(made)) ||
        exists((s: Obj[ConcurrentSet], f: Obj[Consumer[AnyRef]]) => s.forEach(f).isCall(made)))))

val theOwnerCheckCallsCurrentThread = Node.claim(
  "A call of assertOnOwnerThread itself calls only Thread.currentThread.")(
  forall((h: Obj[ThreadHerd]) => ownerCheck(h).itselfCallsOnly(made => Thread.currentThread().isCall(made))))

val theMembershipCheckCallsContains = Node.claim(
  "A call of isOwnerOrHerdThread itself calls only contains of a set.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread]) =>
    h.isOwnerOrHerdThread(t).itselfCallsOnly(made =>
      exists((s: Obj[ConcurrentSet], x: Obj[AnyRef]) => s.contains(x).isCall(made)))))

val aHerdsMethodsOnlyGetAndSetAFlag = Node.claim(
  "Of the methods of an atomic boolean, a method of a herd itself calls only get, and closing set to true.")(
  forall((h: Obj[ThreadHerd], c: Obj[Thread], i: Term[BigInt], made: Term[Invocation], w: Term[BigInt]) =>
    (h.isCalledBy(c.asValue, i) && itselfMakes(made, c.asValue, i, w) && ofAnAtomicBoolean(made)) implies
      (exists((b: Obj[AtomicBoolean]) => b.get().isCall(made)) ||
        (closing(h).by(c).called(i) && exists((b: Obj[AtomicBoolean]) => b.set(true).isCall(made))))))
