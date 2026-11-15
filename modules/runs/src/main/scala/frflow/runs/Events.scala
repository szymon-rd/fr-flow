package frflow.runs

import frflow.*

// What happens at a moment, said of one call and one actor.

/** The call is made at the moment, to be completed later. */
val begun = stated { (c: Term[Invocation], by: Term[Thing], w: Term[BigInt]) =>
  exists((inside: Term[Option[BigInt]]) => steps(w) === make[Step.Makes](by, inside, c)) }

/** The call is made and completed in the step from the moment. */
val doneAtOnce = stated { (c: Term[Invocation], by: Term[Thing], w: Term[BigInt], a: Term[Answer]) =>
  exists((inside: Term[Option[BigInt]], hands: Term[List[Handed]]) =>
    steps(w) === make[Step.Does](by, inside, c, a, hands)) }

/** The call is made at the moment. */
val calledBy = stated { (c: Term[Invocation], by: Term[Thing], w: Term[BigInt]) =>
  begun(c, by, w) || exists((a: Term[Answer]) => doneAtOnce(c, by, w, a)) }

/** The call made at `from` completes at `to` with the answer. */
val completedBy = stated { (c: Term[Invocation], by: Term[Thing], from: Term[BigInt], a: Term[Answer],
    to: Term[BigInt]) =>
  (doneAtOnce(c, by, from, a) && to === from + 1) ||
    (begun(c, by, from) && exists((hands: Term[List[Handed]]) =>
      steps(to - 1) === make[Step.Completes](by, from, a, hands))) }

/** The call made at `from` has completed by the moment. */
val overBy = stated { (by: Term[Thing], from: Term[BigInt], w: Term[BigInt]) =>
  exists((k: Term[BigInt], a: Term[Answer], hands: Term[List[Handed]]) =>
    k < w && steps(k) === make[Step.Completes](by, from, a, hands)) }

/** The step into the moment hands the call to the actor, to run on its own. */
val handedTo = stated { (c: Term[Invocation], to: Term[Thing], w: Term[BigInt]) =>
  (steps(w - 1).on[Step.Makes]((_, _, _) => False)
    .on[Step.Does]((_, _, _, _, hands) => hands.contains(make[Handed](to, c)))
    .on[Step.Completes]((_, _, _, hands) => hands.contains(make[Handed](to, c)))
    .on[Step.Acts](_ => False)
    .on[Step.Rests.type](False): Term[Boolean]) }

/** At the moment the actor, inside its pending call of `outer`, itself makes the call `inner`. */
val madeInside = stated { (outer: Term[Invocation], inner: Term[Invocation], by: Term[Thing], w: Term[BigInt]) =>
  exists((made: Term[BigInt]) => begun(outer, by, made) &&
    (steps(w) === make[Step.Makes](by, some(made), inner) ||
      exists((a: Term[Answer], hands: Term[List[Handed]]) =>
        steps(w) === make[Step.Does](by, some(made), inner, a, hands)))) }
