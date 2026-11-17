package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.OxUnsupervised
import ox.threads.*

// What happens in time, of a scope: the call that runs code in it comes to closing the scope's herd, once the
// code has ended; and closing, by the thread that made the scope, completes.

/** Each call of the code on the scope that the thread makes after the moment is responded to, in time. */
val codeEndsIn = stated { (g: Term[Value], s: Obj[Scope], c: Obj[Thread], from: Term[BigInt]) =>
  forall((m: Term[BigInt]) =>
    (from < m && applicationOf[Any](g, s.asValue).by(c).called(m)) implies
      applicationOf[Any](g, s.asValue).by(c).respondedTo(m)) }

// Of who schedules threads: the thread running code in a scope is given its turn.
val runningInAScopeProceeds = Node.assumption(
  "A call running code in a scope, pending and waiting for no call it made, makes its next event in time.")(
  forall((s: Obj[Scope], g: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    runningIn(s, g).by(c).called(from) implies proceedsFrom(c.asValue, from)))

val whatRunningInAScopeAppliesProceeds = Node.assumption(
  "A call of a function that such a call itself makes, pending and waiting for no call it made, makes its " +
    "next event in time.")(
  forall((s: Obj[Scope], g: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    forall((own: Term[Value], a: Term[BigInt]) =>
      (runningIn(s, g).by(c).called(from) && applicationOf[Any](own).by(c).calledInside(from, a)) implies
        proceedsFrom(c.asValue, a))))

// Of the JDK: a thread's current scope is kept in a `ThreadLocal`, whose `get` and `set` do not block.
val theCurrentScopeResponds = Node.assumption(
  "Reading a thread's current scope, and setting it, are responded to, in time.")(
  forall((s: Obj[OxUnsupervised]) =>
    ox.internal.currentScope.get().responds && ox.internal.currentScope.set(s).responds))

// Of Scala: `herd` is a val of a scope.
val aScopesHerdResponds = Node.assumption("A scope asked for its herd is responded to, in time.")(
  forall((s: Obj[Scope]) => s.seenAs[OxUnsupervised].herd.responds))

val aScopesClosingIsReached = Node.claim(
  "A call running code in a scope calls closing on the scope's herd in time, if each call of the code on the " +
    "scope that its thread makes is responded to.")(
  forall((s: Obj[Scope], g: Term[Value], c: Obj[Thread], from: Term[BigInt]) =>
    (runningIn(s, g).by(c).called(from) && codeEndsIn(g, s, c, from)) implies
      exists((k: Term[BigInt]) => from < k && closing(herdOf(s)).by(c).called(k))))

val aScopesHerdIsClosedInTime = Node.claim(
  "A call running code in a scope, by the thread that made the scope, closes the scope's herd in time, if " +
    "each call of the code on the scope that the thread makes is responded to: closing is called, and is " +
    "responded to.")(
  forall((supervisor: Term[Value], errorMode: Term[Value], parent: Term[Value], locals: Term[Value]) =>
    forall((s: Obj[Scope], g: Term[Value], c: Obj[Thread], a: Term[BigInt], b: Term[BigInt]) =>
      forall((from: Term[BigInt]) =>
        (makingAScope(supervisor, errorMode, parent, locals).by(c).completed(a, Returned(s), b) &&
          runningIn(s, g).by(c).called(from) && codeEndsIn(g, s, c, from)) implies
          exists((k: Term[BigInt]) =>
            from < k && closing(herdOf(s)).by(c).called(k) && closing(herdOf(s)).by(c).respondedTo(k))))))
