package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.{OxError, OxUnsupervised}
import ox.internal.ThreadHerd
import ox.threads.*

// A scope of Ox: an object holding a herd of its own. Code is run in a scope by `scopedWithCapability`, which
// closes the scope's herd before it ends: so what holds of a closed herd holds of the scope's herd from then on.

/** Running code in a scope until the scope ends: `scopedWithCapability(scope)(code)`. */
def runningIn(s: Obj[Scope], code: Term[Value]): Call[Any] =
  Call.of[Any](methodCalled(ox.scopedWithCapability[Any](???)(???)), s.asValue, code)

/** Making a scope of a herd and the rest of what it holds: the `apply` the compiler writes for a case class. */
def makingAScopeOf(herd: Obj[ThreadHerd], rest: Term[Value]*): Call[Scope] =
  Call.of[Scope](methodCalled(OxError[Nothing, [T] =>> T](???, ???, ???, ???, ???, ???)), (herd.asValue +: rest)*)

// Of Scala: the `apply` of a case class is written by the compiler, and is in no tree read. It makes an object
// whose vals hold what it is given.
val aScopeHoldsTheHerdItIsMadeWith = Node.assumption("A scope made with a herd holds that herd.")(
  forall((h: Obj[ThreadHerd], finalizers: Term[Value], supervisor: Term[Value], errorMode: Term[Value]) =>
    forall((parent: Term[Value], locals: Term[Value], s: Obj[Scope]) =>
      makingAScopeOf(h, finalizers, supervisor, errorMode, parent, locals).everyCall((_, reply, _) =>
        (reply === Returned(s)) implies (herdOf(s) === h))))).about(About.objects)

// Of Scala: `herd` is a val of a scope, asked for through the trait it is declared in.
val aScopeGivesTheHerdItHolds = Node.assumption("A scope asked for its herd gives the herd it holds.")(
  forall((s: Obj[Scope]) =>
    s.seenAs[OxUnsupervised].herd.everyCall((_, reply, _) => reply === Returned(herdOf(s))))).about(About.objects)

// Of the JDK: a thread's current scope is kept in a `ThreadLocal`.
val theCurrentScopeIsReadAndSet = Node.assumption("Reading a thread's current scope, and setting it, return.")(
  forall((s: Obj[OxUnsupervised]) =>
    ox.internal.currentScope.get().everyCall((_, reply, _) => exists((x: Term[Value]) =>
      reply === make[Response.Returned](x))) &&
      ox.internal.currentScope.set(s).everyCall((_, reply, _) => reply === Returned(())))).about(About.jdk)

val aScopesHerdIsItsMakers = Node.claim(
  "The herd a scope holds is one whose owner is the thread that made the scope.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((c: Obj[Thread], s: Obj[Scope], from: Moment, to: Moment) =>
      makingAScope(supervisor, errorMode, parent, locals).by(c).completed(from, Returned(s), to) implies
        (owner(herdOf(s)) === c))))
  .from(aScopeHoldsTheHerdItIsMadeWith, aHerdHoldsWhatItWasGiven, currentThreadIsTheCaller)

val aScopeEndsAfterItsHerdIsClosed = Node.claim(
  "Running code in a scope completes only after a call it made, closing the scope's herd, has completed.")(
  forall((s: Obj[Scope], code: Term[Value], c: Obj[Thread]) =>
    forall((from: Moment, ended: Term[Response], to: Moment) =>
      runningIn(s, code).by(c).completed(from, ended, to) implies
        exists((a: Moment, closed: Term[Response], b: Moment) =>
          from < a && b <= to && closing(herdOf(s)).by(c).completed(a, closed, b)))))
  .from(aScopeGivesTheHerdItHolds, theCurrentScopeIsReadAndSet)
