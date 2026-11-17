package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.{AtomicBoolean, AtomicReference}
import ox.internal.ThreadHerd
import ox.threads.*

// What happens in time, of `unsupervised`: it makes a scope and comes to running its code in it; so, once the
// code has ended, the scope's herd is closed.

/** The call returns a value. */
private def returns(reply: Term[Response]): Term[Boolean] =
  exists((x: Term[Value]) => reply === make[Response.Returned](x))

// Of who schedules threads: the thread calling `unsupervised` is given its turn.
val unsupervisedProceeds = Node.assumption(
  "A call of unsupervised, pending and waiting for no call it made, makes its next event in time.")(
  forall((locals: Term[Value], code: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    unsupervisedWith(locals, code).by(c).called(from) implies proceedsFrom(c.asValue, from)))

val makingAScopeProceeds = Node.assumption(
  "A call making a scope, pending and waiting for no call it made, makes its next event in time.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((c: Obj[Thread], from: Term[BigInt]) =>
      makingAScope(supervisor, errorMode, parent, locals).by(c).called(from) implies
        proceedsFrom(c.asValue, from))))

// Of the JDK: these make an object, and neither block nor throw.
val makingAFlagReturnsInTime = Node.assumption("A call that makes an atomic boolean returns, in time.")(
  forall((b: Term[Boolean]) =>
    call(new AtomicBoolean(b)).responds && call(new AtomicBoolean(b)).everyCall((_, reply, _) => returns(reply))))

val makingASetReturnsInTime = Node.assumption("A call that makes a concurrent set returns, in time.")(
  ConcurrentHashMap.newKeySet[AnyRef]().responds &&
    ConcurrentHashMap.newKeySet[AnyRef]().everyCall((_, reply, _) => returns(reply)))

val makingAReferenceReturnsInTime = Node.assumption("A call that makes an atomic reference returns, in time.")(
  forall((x: Obj[AnyRef]) =>
    call(new AtomicReference[AnyRef](x)).responds &&
      call(new AtomicReference[AnyRef](x)).everyCall((_, reply, _) => returns(reply))))

// Of Scala: the `apply` the compiler writes for a case class makes the object, and neither blocks nor throws.
val aScopeIsMadeInTime = Node.assumption(
  "A call that makes a scope of a herd and the rest of what it holds returns, in time.")(
  forall((h: Obj[ThreadHerd], finalizers: Term[Value], supervisor: Term[Value], errorMode: Term[Value]) =>
    forall((parent: Term[Value], locals: Term[Value]) =>
      makingAScopeOf(h, finalizers, supervisor, errorMode, parent, locals).responds &&
        makingAScopeOf(h, finalizers, supervisor, errorMode, parent, locals).everyCall((_, reply, _) =>
          returns(reply)))))

val makingAScopeReturnsInTime = Node.claim("A call making a scope returns a scope, in time.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((c: Obj[Thread], from: Term[BigInt]) =>
      makingAScope(supervisor, errorMode, parent, locals).by(c).called(from) implies
        exists((s: Obj[Scope], to: Term[BigInt]) =>
          makingAScope(supervisor, errorMode, parent, locals).by(c).completed(from, Returned(s), to)))))

val unsupervisedComesToItsScope = Node.claim(
  "A call of unsupervised makes a scope and itself calls running a function in it, in time.")(
  forall((locals: Term[Value], code: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    unsupervisedWith(locals, code).by(c).called(from) implies
      exists((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], s: Obj[Scope]) =>
        exists((g: Term[Value], a: Term[BigInt], b: Term[BigInt], k: Term[BigInt]) =>
          makingAScope(supervisor, errorMode, parent, locals).by(c).completed(a, Returned(s), b) &&
            from < k && runningIn(s, g).by(c).calledInside(from, k)))))

// The function `unsupervised` runs in its scope is one it writes: it applies the code to the scope.
val whatUnsupervisedRunsProceeds = Node.assumption(
  "A call of the function unsupervised runs in its scope, pending and waiting for no call it made, makes its " +
    "next event in time.")(
  forall((locals: Term[Value], code: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    forall((s: Obj[Scope], g: Term[Value], k: Term[BigInt], m: Term[BigInt]) =>
      (unsupervisedWith(locals, code).by(c).called(from) && runningIn(s, g).by(c).calledInside(from, k) &&
        applicationOf[Any](g, s.asValue).by(c).called(m)) implies proceedsFrom(c.asValue, m))))

val whatUnsupervisedRunsEndsOnceItsCodeDoes = Node.claim(
  "A call of the function unsupervised runs in its scope is responded to in time, if each call of the code on " +
    "the scope that its thread makes is.")(
  forall((locals: Term[Value], code: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    forall((s: Obj[Scope], g: Term[Value], k: Term[BigInt], m: Term[BigInt]) =>
      (unsupervisedWith(locals, code).by(c).called(from) && runningIn(s, g).by(c).calledInside(from, k) &&
        codeEndsIn(code, s, c, from) && from < m && applicationOf[Any](g, s.asValue).by(c).called(m)) implies
        applicationOf[Any](g, s.asValue).by(c).respondedTo(m))))

val unsupervisedClosesItsHerdInTime = Node.claim(
  "A call of unsupervised closes the herd of a scope it makes in time, if each call of its code on a scope " +
    "that its thread makes is responded to: closing is called, and is responded to.")(
  forall((locals: Term[Value], code: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    (unsupervisedWith(locals, code).by(c).called(from) &&
      forall((s: Obj[Scope]) => codeEndsIn(code, s, c, from))) implies
      exists((s: Obj[Scope], k: Term[BigInt]) =>
        from < k && closing(herdOf(s)).by(c).called(k) && closing(herdOf(s)).by(c).respondedTo(k))))
