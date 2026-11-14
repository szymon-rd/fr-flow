package scopes

import frflow.*

// What holds of the scopes a program has: the roots, said of the steps the program takes; and what makes them
// hold, said of each kind of step.

/** The scopes when the program starts. */
val atStart = Declaration[Scopes]("the scopes when the program starts")

/** The steps the program's threads have taken on scopes, in order. */
val taken = Declaration[List[Step]]("the steps the program's threads have taken on its scopes, in order")

/** No scope that has ended has a fork not past its body. */
val contained = define { (s: Term[Scopes]) =>
  forall((h: Term[ScopeId], t: Term[ThreadId]) => (ended(s, h) && forkOf(s, t, h)) implies isFinished(s, t)) }

/** A scope opened inside one that has ended has ended. */
val nested = define { (s: Term[Scopes]) =>
  forall((h: Term[ScopeId], inner: Term[ScopeId]) =>
    (isInsideOf(s, inner, h) && ended(s, h)) implies ended(s, inner)) }

/** A fork past its body has no scope open. */
val finishedHasNoneOpen = define { (s: Term[Scopes]) =>
  forall((t: Term[ThreadId], h: Term[ScopeId]) => isFinished(s, t) implies !hasOpen(s, t, h)) }

/** The scope another was opened inside was opened before it: by the same thread, or it is the scope the opener
  * is a fork of.
  */
val parentsAreOlder = define { (s: Term[Scopes]) =>
  forall((h: Term[ScopeId], inner: Term[ScopeId]) =>
    s.scope.get(inner).forall(x => (x.parent === some(h)) implies
      (s.scope.get(h).exists(p => p.opened < x.opened && (p.owner === x.owner || forkOf(s, x.owner, h)))))) }

/** A fork's scope is a scope there is. */
val forksAreOfScopes = define { (s: Term[Scopes]) =>
  forall((t: Term[ThreadId], h: Term[ScopeId]) => forkOf(s, t, h) implies s.scope.get(h).isDefined) }

/** Every scope was opened before now. */
val openedBeforeNow = define { (s: Term[Scopes]) =>
  forall((h: Term[ScopeId]) => s.scope.get(h).forall(x => x.opened < s.clock)) }

/** The scopes are sound: what every step that can be taken keeps. */
val sound = define { (s: Term[Scopes]) =>
  contained(s) && nested(s) && finishedHasNoneOpen(s) && parentsAreOlder(s) && forksAreOfScopes(s) &&
    openedBeforeNow(s) }

/** The program took `e` after `before` and before `after`. */
val tookBetween = stated { (before: Term[List[Step]], e: Term[Step], after: Term[List[Step]]) =>
  taken === before ++ (e :: after) }

val noForkActsAfterItsScopeIsLeft = Node.claim("After a scope is left, no fork of it acts.")(
  forall((before: Term[List[Step]], by: Term[ThreadId], h: Term[ScopeId], between: Term[List[Step]],
      t: Term[ThreadId], after: Term[List[Step]]) =>
    !(taken === before ++ (make[Step.Leave](by, h) :: (between ++ (make[Step.Act](t, h) :: after))))))

val noForkIsMadeAfterItsScopeIsLeft = Node.claim("After a scope is left, no fork is made in it.")(
  forall((before: Term[List[Step]], by: Term[ThreadId], h: Term[ScopeId], between: Term[List[Step]]) =>
    forall((maker: Term[ThreadId], t: Term[ThreadId], after: Term[List[Step]]) =>
      !(taken === before ++ (make[Step.Leave](by, h) :: (between ++ (make[Step.Forks](maker, h, t) :: after)))))))

val scopesAreLeftInsideOut = Node.claim("When a scope is left, every scope opened inside it has ended.")(
  forall((before: Term[List[Step]], by: Term[ThreadId], h: Term[ScopeId], after: Term[List[Step]],
      inner: Term[ScopeId]) =>
    (tookBetween(before, make[Step.Leave](by, h), after) && isInsideOf(ran(atStart, before), inner, h)) implies
      ended(ran(atStart, before), inner)))

val startsSound = Node.claim("A program starts with sound scopes.")(sound(atStart))

val everyStepCanBeTaken = Node.claim("Each step the program takes can be taken when it is.")(
  forall((before: Term[List[Step]], e: Term[Step], after: Term[List[Step]]) =>
    tookBetween(before, e, after) implies canTake(ran(atStart, before), e)))
