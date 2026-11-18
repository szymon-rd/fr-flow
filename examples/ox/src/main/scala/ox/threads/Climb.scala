package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import ox.OxUnsupervised
import ox.internal.ThreadHerd

// The herd's check that its caller is in the tree of scopes. It applies a function of its own, which goes up the
// scopes: it asks a scope for its herd, the herd whether the thread is its owner or one of its threads, the scope
// for its parent, and applies itself to that. What it calls is proven of its tree; what a scope's herd and parent
// do is assumed, the classes of scopes not being read here.

/** The function is the walk up the scopes that a call of a herd's tree check applies itself. */
val walksUp = stated { (g: Term[Value]) =>
  exists((h: Obj[ThreadHerd], c: Obj[Thread], scope: Term[Value], k: Term[BigInt], a: Term[BigInt]) =>
    treeCheck(h).by(c).called(k) && applicationOf[Unit](g, scope).by(c).calledInside(k, a)) }

val theWalkUpCallsFour = Node.claim(
  "The function the tree check applies itself calls only herd and parent of a scope, isOwnerOrHerdThread of a " +
    "herd, and itself.")(
  forall((g: Term[Value], scope: Term[Value]) =>
    walksUp(g) implies applicationOf[Unit](g, scope).itselfCallsOnly(made =>
      exists((s: Obj[OxUnsupervised]) => s.herd.isCall(made)) ||
        exists((s: Obj[OxUnsupervised]) => s.parent.isCall(made)) ||
        exists((h: Obj[ThreadHerd], t: Obj[Thread]) => h.isOwnerOrHerdThread(t).isCall(made)) ||
        exists((s: Term[Value]) => applicationOf[Unit](g, s).isCall(made)))))

// Of Ox's scopes, whose classes are not read here: herd and parent are what a scope was made with.
val aScopesHerdAndParentStayOutOfHerds = Node.assumption(
  "While a thread asks a scope for its herd or for its parent, it neither closes a herd nor removes a thread " +
    "from a herd's set.")(
  forall((s: Obj[OxUnsupervised]) => staysOutOfHerds(s.herd) && staysOutOfHerds(s.parent))).about(About.scopes)

// Of the JDK: none of the four calls back into Ox.
val whatTheChecksAskOfTheJdkStaysOutOfHerds = Node.assumption(
  "While a thread asks for the current thread, for its scope, for a thread's name, or whether a concurrent set " +
    "contains an object, it neither closes a herd nor removes a thread from a herd's set.")(
  forall((t: Obj[Thread], s: Obj[ConcurrentSet], x: Obj[AnyRef]) =>
    staysOutOfHerds(Thread.currentThread()) && staysOutOfHerds(ox.internal.currentScope.get()) &&
      staysOutOfHerds(t.getName()) && staysOutOfHerds(s.contains(x)))).about(About.jdk)

val theMembershipCheckStaysOutOfHerds = Node.claim(
  "While a thread is calling isOwnerOrHerdThread of a herd, it neither closes a herd nor removes a thread from " +
    "a herd's set.")(
  forall((h: Obj[ThreadHerd], t: Obj[Thread]) => staysOutOfHerds(h.isOwnerOrHerdThread(t))))

val theWalkUpStaysOutOfHerds = Node.claim(
  "While a thread is running the function the tree check applies, it neither closes a herd nor removes a " +
    "thread from a herd's set.")(
  forall((g: Term[Value], scope: Term[Value]) =>
    walksUp(g) implies staysOutOfHerds(applicationOf[Unit](g, scope))))
