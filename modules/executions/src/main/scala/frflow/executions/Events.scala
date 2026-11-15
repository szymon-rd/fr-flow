package frflow.executions

import frflow.*
import frflow.values.Value

// What happens at a moment, said of one invocation and one actor.

/** The call is made at the moment, to be completed later. */
val begun = stated { (c: Term[Invocation], by: Term[Value], w: Term[BigInt]) =>
  exists((inside: Term[Option[BigInt]]) => history(w) === make[Event.Invoke](by, inside, c)) }

/** The call is made and completed in the event of the moment. */
val doneAtOnce = stated { (c: Term[Invocation], by: Term[Value], w: Term[BigInt], a: Term[Response]) =>
  exists((inside: Term[Option[BigInt]], spawns: Term[List[Spawn]]) =>
    history(w) === make[Event.Atomic](by, inside, c, a, spawns)) }

/** The call is made at the moment. */
val calledBy = stated { (c: Term[Invocation], by: Term[Value], w: Term[BigInt]) =>
  begun(c, by, w) || exists((a: Term[Response]) => doneAtOnce(c, by, w, a)) }

/** The call made at `from` completes at `to` with the response. */
val completedBy = stated { (c: Term[Invocation], by: Term[Value], from: Term[BigInt], a: Term[Response],
    to: Term[BigInt]) =>
  (doneAtOnce(c, by, from, a) && to === from + 1) ||
    (begun(c, by, from) && exists((spawns: Term[List[Spawn]]) =>
      history(to - 1) === make[Event.Respond](by, from, a, spawns))) }

/** The call made at `from` has completed by the moment. */
val overBy = stated { (by: Term[Value], from: Term[BigInt], w: Term[BigInt]) =>
  exists((k: Term[BigInt], a: Term[Response], spawns: Term[List[Spawn]]) =>
    k < w && history(k) === make[Event.Respond](by, from, a, spawns)) }

/** The event into the moment spawns the call for the actor, to make on its own. */
val spawnedTo = stated { (c: Term[Invocation], to: Term[Value], w: Term[BigInt]) =>
  (history(w - 1).on[Event.Invoke]((_, _, _) => False)
    .on[Event.Atomic]((_, _, _, _, spawns) => spawns.contains(make[Spawn](to, c)))
    .on[Event.Respond]((_, _, _, spawns) => spawns.contains(make[Spawn](to, c)))
    .on[Event.Internal](_ => False)
    .on[Event.Stutter.type](False): Term[Boolean]) }

/** At the moment the actor, inside its pending call of `outer`, itself makes the call `inner`. */
val madeInside = stated { (outer: Term[Invocation], inner: Term[Invocation], by: Term[Value], w: Term[BigInt]) =>
  exists((made: Term[BigInt]) => begun(outer, by, made) &&
    (history(w) === make[Event.Invoke](by, some(made), inner) ||
      exists((a: Term[Response], spawns: Term[List[Spawn]]) =>
        history(w) === make[Event.Atomic](by, some(made), inner, a, spawns)))) }
