package scopes

import frflow.*

// The scopes and forks of a running program, as little of them as says whether a fork can still be running when
// its scope has been left: who opened a scope and inside which, whether it has ended; which scope a fork was made
// in, and whether it is past its body. Nothing of a scope's result, of interruption or of time is here.

/** Where a fork is: running (from when it is made in its scope until its body is over), or past its body. */
enum Life derives FrSpec:
  case Running, Finished

/** A scope: the thread that opened it, the scope that thread was in when it did (if any), when it was opened, and
  * whether it has ended.
  */
final case class Scope(owner: ThreadId, parent: Option[ScopeId], opened: BigInt, ended: Boolean) derives FrSpec

/** A fork: the scope it was made in, and where it is in its life. */
final case class Fork(scope: ScopeId, life: Life) derives FrSpec

/** Every scope opened so far and every fork made so far, and the time. */
final case class Scopes(scope: Map[ScopeId, Scope], fork: Map[ThreadId, Fork], clock: BigInt) derives FrSpec

/** What a thread does to the scopes, or is seen to do.
  *   - `Open`: it opens a scope (`supervised`, `unsupervised` begin), inside `parent`.
  *   - `Forks`: it makes a fork in a scope: `thread`, which will run the fork's body.
  *   - `Finish`: a fork is past its body, however the body ended.
  *   - `End`: the opener finds every fork of the scope past its body.
  *   - `Leave`: the opener is given the scope's result or what it throws (`supervised`, `unsupervised` return).
  *   - `Act`: a fork does something of its body.
  */
enum Step derives FrSpec:
  case Open(by: ThreadId, scope: ScopeId, parent: Option[ScopeId])
  case Forks(by: ThreadId, scope: ScopeId, thread: ThreadId)
  case Finish(thread: ThreadId)
  case End(by: ThreadId, scope: ScopeId)
  case Leave(by: ThreadId, scope: ScopeId)
  case Act(thread: ThreadId, scope: ScopeId)

/** A thread has a scope open: it opened it, and the scope has not ended. */
val hasOpen = define { (s: Term[Scopes], w: Term[ThreadId], h: Term[ScopeId]) =>
  s.scope.get(h).exists(x => x.owner === w && !x.ended) }

/** A scope has ended. */
val ended = define { (s: Term[Scopes], h: Term[ScopeId]) => s.scope.get(h).exists(x => x.ended) }

/** When a scope was opened. */
val openedAt = define { (s: Term[Scopes], h: Term[ScopeId]) =>
  s.scope.get(h).fold(BigInt(0): Term[BigInt])(x => x.opened) }

/** A thread's innermost scope: one it has open, opened after every other it has open. */
val innermost = define { (s: Term[Scopes], w: Term[ThreadId], h: Term[ScopeId]) =>
  hasOpen(s, w, h) &&
    forall((other: Term[ScopeId]) => hasOpen(s, w, other) implies openedAt(s, other) <= openedAt(s, h)) }

/** A thread has no scope open. */
val hasNoneOpen = define { (s: Term[Scopes], w: Term[ThreadId]) =>
  forall((h: Term[ScopeId]) => !hasOpen(s, w, h)) }

/** A thread is a fork of a scope. */
val forkOf = define { (s: Term[Scopes], t: Term[ThreadId], h: Term[ScopeId]) =>
  s.fork.get(t).exists(f => f.scope === h) }

/** A fork is past its body. */
val isFinished = define { (s: Term[Scopes], t: Term[ThreadId]) =>
  s.fork.get(t).exists(f => f.life === Life.Finished) }

/** A thread is a fork of a scope, not yet past its body. */
val runsIn = define { (s: Term[Scopes], t: Term[ThreadId], h: Term[ScopeId]) =>
  s.fork.get(t).exists(f => f.scope === h && f.life === Life.Running) }

/** A thread can take a step of its own: it is no fork, or a fork not past its body. */
val isLive = define { (s: Term[Scopes], w: Term[ThreadId]) => s.fork.get(w).forall(f => f.life === Life.Running) }

/** A thread is inside a scope: it has it open, or it is a fork of it not past its body. */
val isInside = define { (s: Term[Scopes], w: Term[ThreadId], h: Term[ScopeId]) =>
  hasOpen(s, w, h) || runsIn(s, w, h) }

/** A scope was opened inside another. */
val isInsideOf = define { (s: Term[Scopes], inner: Term[ScopeId], h: Term[ScopeId]) =>
  s.scope.get(inner).exists(x => x.parent === some(h)) }
