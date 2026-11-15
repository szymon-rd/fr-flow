package frflow.executions

import frflow.{Call as _, *}
import frflow.values.{AsValue, Obj, Value}

/** A moment of the execution. */
type World = Term[BigInt]

/** A method or function of real code applied: which calls of an execution a statement means. `A` is what it
  * returns; `actor` is who makes it, or anyone.
  */
final class Call[A](val method: String, val arguments: List[Term[Value]], val actor: Option[Term[Value]]):
  /** The call as the execution has it. */
  val invocation: Term[Invocation] =
    make[Invocation](method, arguments.foldRight(Nil: Term[List[Value]])(_ :: _))

  /** The same calls, made by `t`. */
  def by[C](t: Obj[C]): Call[A] = new Call(method, arguments, Some(t.asValue))

  private def some(p: Term[Value] => Term[Boolean]): Term[Boolean] =
    actor.fold(exists((who: Term[Value]) => p(who)))(p)

  /** A call is made at `w`. */
  def called(w: World)(using Stating): Term[Boolean] = some(calledBy(invocation, _, w))

  /** The call made at `from` completes at `to` with `response`. */
  def completed(from: World, response: Term[Response], to: World)(using Stating): Term[Boolean] =
    some(completedBy(invocation, _, from, response, to))

  /** `holds` of every completed call. */
  def everyCall(holds: (World, Term[Response], World) => Term[Boolean])(using Stating): Term[Boolean] =
    forall((from: Term[BigInt], response: Term[Response], to: Term[BigInt]) =>
      completed(from, response, to) implies holds(from, response, to))

  /** What a library calls atomic: every call that returns takes effect at one moment during it. `effect` is said
    * of the moment before the effect and the moment after it. The call still takes time: others act meanwhile.
    */
  def atomic(effect: (World, World) => Term[Boolean])(using Stating): Term[Boolean] =
    forall((from: Term[BigInt], value: Term[Value], to: Term[BigInt]) =>
      completed(from, make[Response.Returned](value), to) implies
        exists((m: Term[BigInt]) => from <= m && m < to && effect(m, m + 1)))

  /** The call is in progress at `w`: it is made at `w`, or was made before and is not over. */
  def inProgress(w: World)(using Stating): Term[Boolean] = called(w) || pendingAt(w)

  /** A call has returned by `w`. */
  def returnedBefore(w: World)(using Stating): Term[Boolean] =
    exists((from: Term[BigInt], value: Term[Value], to: Term[BigInt]) =>
      to <= w && completed(from, make[Response.Returned](value), to))

  /** A call was made before `w`. */
  def calledBefore(w: World)(using Stating): Term[Boolean] = exists((m: Term[BigInt]) => m < w && called(m))

  /** A call made before `w` has not completed by `w`. */
  def pendingAt(w: World)(using Stating): Term[Boolean] = exists((m: Term[BigInt]) => pendingSince(m, w))

  /** The call made at `from` has not completed by `w`. */
  def pendingSince(from: World, w: World)(using Stating): Term[Boolean] =
    from < w && some(who => begun(invocation, who, from) && !overBy(who, from, w))

  /** A call is made at a moment from `from` to `to`. */
  def calledWithin(from: World, to: World)(using Stating): Term[Boolean] =
    exists((m: Term[BigInt]) => from <= m && m <= to && called(m))

  /** A call made and completed from `from` to `to` returned `value`. */
  def returnedWithin(value: Term[A], from: World, to: World)(using Stating, AsValue[A]): Term[Boolean] =
    exists((a: Term[BigInt], b: Term[BigInt]) => from <= a && b <= to && completed(a, Returned(value), b))

  /** There is a moment after `w` at which no call is pending. */
  def settles(w: World)(using Stating): Term[Boolean] =
    exists((later: Term[BigInt]) => w < later && !pendingAt(later))

  /** The event into `w` spawns the call for its actor, to make on its own. */
  def spawned(w: World)(using Stating): Term[Boolean] = some(spawnedTo(invocation, _, w))

  /** At `w` a pending call of this makes the call `inner` itself, not through another call. */
  def calls[B](inner: Call[B], w: World)(using Stating): Term[Boolean] =
    some(who => madeInside(invocation, inner.invocation, who, w))

  /** The call made at `made` by this call's actor itself makes this call at `w`. */
  def calledInside(made: World, w: World)(using Stating): Term[Boolean] = some(itselfMakes(invocation, _, made, w))

  /** A call made and completed from `from` to `to`. */
  def completedWithin(from: World, to: World)(using Stating): Term[Boolean] =
    exists((a: Term[BigInt], response: Term[Response], b: Term[BigInt]) =>
      from <= a && b <= to && completed(a, response, b))

object Call:
  /** The call of `method` with `arguments`, by anyone. */
  def of[A](method: String, arguments: Term[Value]*): Call[A] = new Call(method, arguments.toList, None)

/** The call returned the value. */
def Returned[A](value: Term[A])(using as: AsValue[A]): Term[Response] = make[Response.Returned](as(value))

/** The call threw the exception. */
def Threw[C <: Throwable](exception: Obj[C]): Term[Response] = make[Response.Threw](exception.asValue)

/** `holds` at `w` or at some later moment. */
def eventually(w: World)(holds: World => Term[Boolean]): Term[Boolean] =
  exists((later: Term[BigInt]) => w <= later && holds(later))

/** What has a value at each moment, read at one with `at`. */
final class Changing[A](read: World => Term[A]):
  def at(w: World): Term[A] = read(w)
