package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.executions.*
import frflow.values.*
import ox.{Ox, OxError}
import ox.internal.ThreadHerd
import ox.threads.*

// `fork` starts a fork by `forkError`, in the scope `asNoErrorMode` gives, which holds the same herd; and
// `forkError` calls `startThread` on the herd of its scope. So `fork` in a scope whose herd is closed does not
// return. A scope is an object of Ox's class `OxError`: its methods and its vals are read from Ox's code.

/** Starting a fork of the code in the scope: `fork(code)(using s)`. */
def forking(code: Term[Value], s: Obj[Scope]): Call[Any] =
  Call.of[Any](methodCalled(ox.fork[Any](???)(using ???)), code, s.asValue)

/** Starting a fork of the code in the scope, with its error mode: `forkError(using s)(code)`. */
def forkingError(s: Obj[Scope], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.forkError[Nothing, [T] =>> T, Any](using ???)(???)), s.asValue, code)

/** Starting a user fork of the code in the scope: `forkUser(code)(using s)`. */
def forkingUser(code: Term[Value], s: Obj[Scope]): Call[Any] =
  Call.of[Any](methodCalled(ox.forkUser[Any](???)(using ???)), code, s.asValue)

/** Starting a user fork of the code in the scope, with its error mode: `forkUserError(using s)(code)`. */
def forkingUserError(s: Obj[Scope], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.forkUserError[Nothing, [T] =>> T, Any](using ???)(???)), s.asValue, code)

/** The scope without an error mode: `s.asNoErrorMode`. */
def withoutErrorMode(s: Obj[Scope]): Call[Scope] = Call.of[Scope](methodOf[Ox](_.asNoErrorMode), s.asValue)

/** The scope is an object of the class of scopes: one made, at some moment, as an object of that class. */
val scopeMade = stated { (s: Obj[Scope]) =>
  exists((w: Term[BigInt]) => madeBefore(s.asValue, classOf[OxError[?, ?]].getName, w)) }

// Of Scala: the `apply` the compiler writes for a case class makes the object by the class's constructor.
val aScopeIsConstructed = Node.assumption(
  "A scope made with a herd is one that a call of its class's constructor has returned.")(
  forall((h: Obj[ThreadHerd], finalizers: Term[Value], supervisor: Term[Value], errorMode: Term[Value]) =>
    forall((parent: Term[Value], locals: Term[Value], s: Obj[Scope]) =>
      makingAScopeOf(h, finalizers, supervisor, errorMode, parent, locals).everyCall((_, reply, to) =>
        (reply === Returned(s)) implies s.isConstructed(to)))))

// Of Scala: a val is assigned once, when the object is made.
val aScopeKeepsItsFields = Node.assumption("Each val of a scope is read as what the scope holds.")(
  forall((s: Obj[Scope]) => s.readsItsValsAsHeld))

val aConstructedScopeIsMade = Node.claim(
  "A scope that a call of its class's constructor has returned is an object of that class.")(
  forall((s: Obj[Scope], w: Term[BigInt]) => s.isConstructed(w) implies scopeMade(s)))

val aScopeMadeIsAnObject = Node.claim(
  "What making a scope returns is an object of the class of scopes.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
      makingAScope(supervisor, errorMode, parent, locals).completed(from, Returned(s), to) implies
        scopeMade(s))))

val asNoErrorModeKeepsTheHerd = Node.claim(
  "A scope asked for itself without an error mode gives a scope, an object of the class of scopes, that " +
    "holds the same herd.")(
  forall((s: Obj[Scope], from: Term[BigInt], other: Obj[Scope], to: Term[BigInt]) =>
    (scopeMade(s) && withoutErrorMode(s).completed(from, Returned(other), to)) implies
      (scopeMade(other) && (herdOf(other) === herdOf(s)))))

val forkErrorStartsAThread = Node.claim(
  "A call of forkError in a scope returns only after a call of startThread on the scope's herd, that it made " +
    "itself, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Term[BigInt], fork: Term[Value], to: Term[BigInt]) =>
      (scopeMade(s) && forkingError(s, code).by(c).completed(from, make[Response.Returned](fork), to)) implies
        exists((run: Obj[Code], a: Term[BigInt], b: Term[BigInt]) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).calledInside(from, a) &&
            starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))

val forkStartsAThread = Node.claim(
  "A call of fork in a scope returns only after a call of startThread on the scope's herd, made during it by " +
    "its thread, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Term[BigInt], fork: Term[Value], to: Term[BigInt]) =>
      (scopeMade(s) && forking(code, s).by(c).completed(from, make[Response.Returned](fork), to)) implies
        exists((run: Obj[Code], a: Term[BigInt], b: Term[BigInt]) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))

val forkIsRefusedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, a call of fork in the scope it made does not return.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((code: Term[Value], d: Obj[Thread], m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (supervisedMade(c, s, from, to) && to <= m && forking(code, s).by(d).called(m)) implies
        !forking(code, s).by(d).completed(m, make[Response.Returned](fork), w))))

val forkUserErrorStartsAThread = Node.claim(
  "A call of forkUserError in a scope returns only after a call of startThread on the scope's herd, that it " +
    "made itself, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Term[BigInt], fork: Term[Value], to: Term[BigInt]) =>
      (scopeMade(s) &&
        forkingUserError(s, code).by(c).completed(from, make[Response.Returned](fork), to)) implies
        exists((run: Obj[Code], a: Term[BigInt], b: Term[BigInt]) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).calledInside(from, a) &&
            starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))

val forkUserStartsAThread = Node.claim(
  "A call of forkUser in a scope returns only after a call of startThread on the scope's herd, made during it " +
    "by its thread, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Term[BigInt], fork: Term[Value], to: Term[BigInt]) =>
      (scopeMade(s) && forkingUser(code, s).by(c).completed(from, make[Response.Returned](fork), to)) implies
        exists((run: Obj[Code], a: Term[BigInt], b: Term[BigInt]) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))

val forkUserIsRefusedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, a call of forkUser in the scope it made does not return.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((code: Term[Value], d: Obj[Thread], m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (supervisedMade(c, s, from, to) && to <= m && forkingUser(code, s).by(d).called(m)) implies
        !forkingUser(code, s).by(d).completed(m, make[Response.Returned](fork), w))))
