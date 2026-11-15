package frflow.runs

import frflow.*

/** A moment of the run. */
type World = Term[BigInt]

/** A method or function of real code applied: which calls of a run a statement means. `A` is what it returns; `by`
  * is who makes it, or anyone.
  */
final class Call[A](val what: String, val takes: List[Term[Thing]], val actor: Option[Term[Thing]]):
  /** The call as the run has it. */
  val invoked: Term[Invocation] = make[Invocation](what, takes.foldRight(Nil: Term[List[Thing]])(_ :: _))

  /** The same calls, made by `t`. */
  def by[C](t: Obj[C]): Call[A] = new Call(what, takes, Some(t.thing))

  private def some(p: Term[Thing] => Term[Boolean]): Term[Boolean] =
    actor.fold(exists((who: Term[Thing]) => p(who)))(p)

  private def each(p: Term[Thing] => Term[Boolean]): Term[Boolean] =
    actor.fold(forall((who: Term[Thing]) => p(who)))(p)

  /** A call is made at `w`. */
  def called(w: World)(using Stating): Term[Boolean] = some(calledBy(invoked, _, w))

  /** The call made at `from` completes at `to` with `answer`. */
  def completed(from: World, answer: Term[Answer], to: World)(using Stating): Term[Boolean] =
    some(completedBy(invoked, _, from, answer, to))

  /** `holds` of every completed call. */
  def everyCall(holds: (World, Term[Answer], World) => Term[Boolean])(using Stating): Term[Boolean] =
    forall((from: Term[BigInt], answer: Term[Answer], to: Term[BigInt]) =>
      completed(from, answer, to) implies holds(from, answer, to))

  /** Every call completes at the very next moment. */
  def atomic(using Stating): Term[Boolean] = forall((w: Term[BigInt]) =>
    each(who => calledBy(invoked, who, w) implies exists((a: Term[Answer]) => doneAtOnce(invoked, who, w, a))))

  /** A call was made before `w`. */
  def calledBefore(w: World)(using Stating): Term[Boolean] = exists((m: Term[BigInt]) => m < w && called(m))

  /** A call made before `w` has not completed by `w`. */
  def pendingAt(w: World)(using Stating): Term[Boolean] = exists((m: Term[BigInt]) =>
    m < w && some(who => begun(invoked, who, m) && !overBy(who, m, w)))

  /** A call is made at a moment from `from` to `to`. */
  def calledWithin(from: World, to: World)(using Stating): Term[Boolean] =
    exists((m: Term[BigInt]) => from <= m && m <= to && called(m))

  /** A call made and completed from `from` to `to` returned `value`. */
  def returnedWithin(value: Term[A], from: World, to: World)(using Stating, AsThing[A]): Term[Boolean] =
    exists((a: Term[BigInt], b: Term[BigInt]) => from <= a && b <= to && completed(a, Returned(value), b))

  /** There is a moment after `w` at which no call is pending. */
  def settles(w: World)(using Stating): Term[Boolean] =
    exists((later: Term[BigInt]) => w < later && !pendingAt(later))

  /** The step into `w` hands the call to its actor to run on its own. */
  def spawned(w: World)(using Stating): Term[Boolean] = some(handedTo(invoked, _, w))

  /** At `w` a pending call of this makes the call `inner` itself, not through another call. */
  def calls[B](inner: Call[B], w: World)(using Stating): Term[Boolean] =
    some(who => madeInside(invoked, inner.invoked, who, w))

  /** A call made and completed from `from` to `to`. */
  def completedWithin(from: World, to: World)(using Stating): Term[Boolean] =
    exists((a: Term[BigInt], answer: Term[Answer], b: Term[BigInt]) =>
      from <= a && b <= to && completed(a, answer, b))

object Call:
  /** The call of `what` taking `takes`, by anyone. */
  def of[A](what: String, takes: Term[Thing]*): Call[A] = new Call(what, takes.toList, None)

/** The call returned the value. */
def Returned[A](value: Term[A])(using as: AsThing[A]): Term[Answer] = make[Answer.Returned](as(value))

/** The call threw the exception. */
def Threw[C <: Throwable](exception: Obj[C]): Term[Answer] = make[Answer.Threw](exception.thing)

/** `holds` at `w` or at some later moment. */
def eventually(w: World)(holds: World => Term[Boolean]): Term[Boolean] =
  exists((later: Term[BigInt]) => w <= later && holds(later))

/** What has a value at each moment, read at one with `at`. */
final class Changing[A](read: World => Term[A]):
  def at(w: World): Term[A] = read(w)

