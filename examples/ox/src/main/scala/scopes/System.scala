package scopes

import frflow.*

// What a step needs, and what it leaves: the system the statements are about.

/** The scope a thread opens a new one inside: its innermost scope; or, if it has none open, the scope it is a
  * fork of; or none.
  */
val opensInside = define { (s: Term[Scopes], w: Term[ThreadId], parent: Term[Option[ScopeId]]) =>
  parent.fold(hasNoneOpen(s, w) && forall((h: Term[ScopeId]) => !runsIn(s, w, h)))(p =>
    innermost(s, w, p) || (hasNoneOpen(s, w) && runsIn(s, w, p))) }

/** A thread is new to the scopes: no fork, and the opener of no scope. */
val isNew = define { (s: Term[Scopes], c: Term[ThreadId]) =>
  s.fork.get(c).isEmpty && forall((h: Term[ScopeId]) => s.scope.get(h).forall(x => x.owner =!= c)) }

/** Every fork of a scope is past its body. */
val allFinished = define { (s: Term[Scopes], h: Term[ScopeId]) =>
  forall((t: Term[ThreadId]) => s.fork.get(t).forall(f => (f.scope === h) implies (f.life === Life.Finished))) }

/** A step can be taken.
  *   - A scope is opened under a name not yet used, by a thread that can take a step, inside its place.
  *   - A fork is made in a scope by a thread inside it, of a thread new to the scopes.
  *   - A fork not past its body finishes it, with no scope open.
  *   - A scope is ended by its opener, as its innermost, when every fork of it is past its body.
  *   - A scope is left by its opener once it has ended.
  *   - A fork acts while it is not past its body.
  */
val canTake = define { (s: Term[Scopes], e: Term[Step]) =>
  e.on[Step.Open]((by, scope, parent) =>
      s.scope.get(scope).isEmpty && isLive(s, by) && opensInside(s, by, parent))
    .on[Step.Forks]((by, scope, thread) => isInside(s, by, scope) && isNew(s, thread))
    .on[Step.Finish](thread => s.fork.get(thread).exists(f => f.life === Life.Running) && hasNoneOpen(s, thread))
    .on[Step.End]((by, scope) => innermost(s, by, scope) && allFinished(s, scope))
    .on[Step.Leave]((by, scope) => s.scope.get(scope).exists(x => x.owner === by && x.ended))
    .on[Step.Act]((thread, scope) => runsIn(s, thread, scope)) }

/** The scopes after a step: seeing a scope left or a fork act changes nothing. */
val afterStep = define { (s: Term[Scopes], e: Term[Step]) =>
  e.on[Step.Open]((by, scope, parent) =>
      s.updated(_.scope, s.scope.updated(scope, make[Scope](by, parent, s.clock, False)))
        .updated(_.clock, s.clock + 1))
    .on[Step.Forks]((_, scope, thread) =>
      s.updated(_.fork, s.fork.updated(thread, make[Fork](scope, Life.Running))))
    .on[Step.Finish](thread =>
      s.updated(_.fork, s.fork.get(thread).fold(s.fork)(f =>
        s.fork.updated(thread, f.updated(_.life, Life.Finished)))))
    .on[Step.End]((_, scope) =>
      s.updated(_.scope, s.scope.get(scope).fold(s.scope)(x => s.scope.updated(scope, x.updated(_.ended, True)))))
    .on[Step.Leave]((_, _) => s)
    .on[Step.Act]((_, _) => s) }

/** The scopes after some steps, in order, from a state. */
val ran = define { (start: Term[Scopes], steps: Term[List[Step]]) =>
  steps.foldLeft(start)((s, e) => afterStep(s, e)) }
