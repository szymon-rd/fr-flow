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
    .on[Event.Make]((_, _, _, _, _) => False)
    .on[Event.Read]((_, _, _, _, _) => False)
    .on[Event.Mark]((_, _, _, _) => False)
    .on[Event.Write]((_, _, _, _, _) => False)
    .on[Event.Enter]((_, _, _, _, _) => False)
    .on[Event.Internal](_ => False)
    .on[Event.Stutter.type](False): Term[Boolean]) }

/** At the moment the actor, inside its pending call of `outer`, itself makes the call `inner`. */
val madeInside = stated { (outer: Term[Invocation], inner: Term[Invocation], by: Term[Value], w: Term[BigInt]) =>
  exists((made: Term[BigInt]) => begun(outer, by, made) &&
    (history(w) === make[Event.Invoke](by, some(made), inner) ||
      exists((a: Term[Response], spawns: Term[List[Spawn]]) =>
        history(w) === make[Event.Atomic](by, some(made), inner, a, spawns)))) }

/** The call made at `made` by the actor itself makes the call `inner` at the moment: not a call it makes does. */
val itselfMakes = stated { (inner: Term[Invocation], by: Term[Value], made: Term[BigInt], w: Term[BigInt]) =>
  history(w) === make[Event.Invoke](by, some(made), inner) ||
    exists((a: Term[Response], spawns: Term[List[Spawn]]) =>
      history(w) === make[Event.Atomic](by, some(made), inner, a, spawns)) }

/** The actor does something at the moment, inside the call made at `inside`: it makes a call or an object, or
  * reads, marks, writes or enters a field.
  */
val does = stated { (by: Term[Value], inside: Term[Option[BigInt]], w: Term[BigInt]) =>
  (history(w).on[Event.Invoke]((b, i, _) => b === by && i === inside)
    .on[Event.Atomic]((b, i, _, _, _) => b === by && i === inside)
    .on[Event.Respond]((_, _, _, _) => False)
    .on[Event.Make]((b, i, _, _, _) => b === by && i === inside)
    .on[Event.Read]((b, i, _, _, _) => b === by && i === inside)
    .on[Event.Mark]((b, i, _, _) => b === by && i === inside)
    .on[Event.Write]((b, i, _, _, _) => b === by && i === inside)
    .on[Event.Enter]((b, i, _, _, _) => b === by && i === inside)
    .on[Event.Internal](_ => False)
    .on[Event.Stutter.type](False): Term[Boolean]) }

/** The call made at `from` by the actor makes an event of its own at the moment: it does something itself, or is
  * responded to.
  */
val actsItself = stated { (by: Term[Value], from: Term[BigInt], w: Term[BigInt]) =>
  does(by, some(from), w) || exists((a: Term[Response], spawns: Term[List[Spawn]]) =>
    history(w) === make[Event.Respond](by, from, a, spawns)) }

/** At the moment, the call made at `from` by the actor waits for a call it made itself: one not yet over. */
val waitsForACall = stated { (by: Term[Value], from: Term[BigInt], w: Term[BigInt]) =>
  exists((m: Term[BigInt], inner: Term[Invocation]) =>
    m < w && history(m) === make[Event.Invoke](by, some(from), inner) && !overBy(by, m, w)) }

/** The actor does one thing at a time: what it does while a call of its own is pending, that call does itself,
  * or the actor does while a call that call itself made is pending.
  */
val oneAtATime = stated { (by: Term[Value]) =>
  forall((outer: Term[Invocation], from: Term[BigInt], inside: Term[Option[BigInt]], w: Term[BigInt]) =>
    (from < w && begun(outer, by, from) && !overBy(by, from, w) && does(by, inside, w)) implies
      (inside === some(from) ||
        exists((between: Term[Invocation], m: Term[BigInt]) =>
          from < m && m < w && history(m) === make[Event.Invoke](by, some(from), between) && !overBy(by, m, w)))) }

/** The call made at `from` by the actor itself makes the object. */
val itselfCreates = stated { (made: Term[Value], by: Term[Value], from: Term[BigInt]) =>
  exists((m: Term[BigInt], cls: Term[String], holding: Term[List[Held]]) =>
    history(m) === make[Event.Make](by, some(from), made, cls, holding)) }

/** The actor reads or writes a field of the object at the moment. */
val touches = stated { (on: Term[Value], by: Term[Value], w: Term[BigInt]) =>
  exists((inside: Term[Option[BigInt]], field: Term[String], value: Term[Value]) =>
    history(w) === make[Event.Read](by, inside, on, field, value) ||
      history(w) === make[Event.Write](by, inside, on, field, value)) }

/** A call of the method named `method` is made at `w` on `on`, with whatever else it is given. */
val calledOn = stated { (on: Term[Value], method: Term[String], w: Term[BigInt]) =>
  exists((rest: Term[List[Value]], by: Term[Value]) => calledBy(make[Invocation](method, on :: rest), by, w)) }

/** An object of the class, named by the value, has been made before the moment. */
val madeBefore = stated { (made: Term[Value], cls: Term[String], w: Term[BigInt]) =>
  exists((m: Term[BigInt], by: Term[Value], inside: Term[Option[BigInt]], holding: Term[List[Held]]) =>
    m < w && history(m) === make[Event.Make](by, inside, made, cls, holding)) }

/** Every read of the field of the object finds the value. */
val readAs = stated { (on: Term[Value], field: Term[String], value: Term[Value]) =>
  forall((w: Term[BigInt], by: Term[Value], inside: Term[Option[BigInt]], found: Term[Value]) =>
    (history(w) === make[Event.Read](by, inside, on, field, found)) implies (found === value)) }

/** Every write of the field of the object writes the value. */
val writtenAs = stated { (on: Term[Value], field: Term[String], value: Term[Value]) =>
  forall((w: Term[BigInt], by: Term[Value], inside: Term[Option[BigInt]], written: Term[Value]) =>
    (history(w) === make[Event.Write](by, inside, on, field, written)) implies (written === value)) }
