package frflow.eval.flow

import frflow.*
import frflow.dsl.term.Lift
import frflow.eval.flow.Shelf.{held, putting}

/** Programs of loops and errors over the shelf: `each`, `collect`, `fold`, a condition, `raise` and `handle`,
  * `attempt`, a failing model's call, `retry`.
  */
object Steps:
  private def nums(ns: Int*): Term[List[BigInt]] = Lift.constant(ns.toList.map(BigInt(_)))
  private val down: Term[Trouble] = Lift.constant(Trouble.Down)
  private def ok(v: Any, shelf: List[Int], time: Int) = (Right(v), shelf.map(BigInt(_)), BigInt(time))
  private def failed(e: Any, shelf: List[Int], time: Int) = (Left(e), shelf.map(BigInt(_)), BigInt(time))

  val collectAndFold = Shelved[BigInt]("collect, then fold over what it gave", Nil, ok(BigInt(18), List(1, 2, 3), 0))(
    Flow.collect(nums(1, 2, 3))(x => putting(x).as(x + 1)).flatMap(ys =>
      Flow.fold(ys, 0: Term[BigInt])((acc, y) => held.map(h => acc + y + h.length))))

  val eachAndCondition = Shelved[BigInt]("each, then a branch by what the shelf holds", Nil, ok(BigInt(1), List(4, 5),
    0))(Flow.each(nums(4, 5))(putting).flatMap(_ => Flow.ifM(held.map(_.length > 1))(Flow.pure(1), Flow.pure(0))))

  val handled = Shelved[BigInt]("an error raised, given to the handler of its type", Nil, ok(BigInt(7), List(2, 9),
    0))(putting(2).flatMap(_ => held.flatMap(h =>
      Flow.cond(h.length > 0)(Flow.raise(make[Trouble.TooBig](h.length)), Flow.pure(0))))
      .handle[Trouble](_ => putting(9).as(7)))

  val otherType = Shelved[BigInt]("an error passes a handler of another type by, to its own type's", Nil,
    ok(BigInt(2), Nil, 0))(Flow.raise[Trouble, BigInt](down).handle[String](_ => Flow.pure(1))
      .handle[Trouble](_ => Flow.pure(2)))

  val unhandled = Shelved[BigInt]("an error raised and not handled: the run fails with it", Nil,
    failed(Trouble.TooBig(1), List(3), 0))(putting(3).flatMap(_ => held.flatMap(h =>
      Flow.raise[Trouble, BigInt](make[Trouble.TooBig](h.length)))))

  val attempted = Shelved[Either[Trouble, BigInt]]("attempt: the error on the left, the run going on", Nil,
    ok(Left(Trouble.Down), List(1, 6), 0))(
      putting(1).flatMap(_ => Flow.raise[Trouble, BigInt](down)).attempt[Trouble].flatMap(e => putting(6).as(e)))

  val failingCall = Shelved[BigInt]("a failing model's second call fails: the first stays done", List(false, true),
    failed(Trouble.Down, List(1), 0))(putting(1).flatMap(_ => putting(2).flatMap(_ => Flow.pure(3))))

  val failingHandled = Shelved[BigInt]("a failing call's error handled", List(true), ok(BigInt(0), Nil, 0))(
    held.map(_.length).handle[Trouble](_ => Flow.pure(0)))

  val retried = Shelved[BigInt]("retry: tried again after each wait while it fails", List(true, true, false),
    ok(BigInt(5), List(5), 3))(Flow.retry[Trouble, BigInt](Clock.sleep, List(1, 2))(putting(5).as(5)))

  val retriedOut = Shelved[BigInt]("retry: every try failed, the last one's error", List(true, true, true),
    failed(Trouble.Down, Nil, 3))(Flow.retry[Trouble, BigInt](Clock.sleep, List(1, 2))(putting(5).as(5)))

  val all: List[Shelved[?]] =
    List(collectAndFold, eachAndCondition, handled, otherType, unhandled, attempted, failingCall, failingHandled,
      retried, retriedOut)
