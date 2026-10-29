package frflow.eval.flow

import frflow.*
import frflow.dsl.term.Lift

/** Programs of loops and errors over the shelf: `each`, `collect`, `fold`, a condition, `raise` and `handle`,
  * `attempt`, a failing model's call, `retry`.
  */
object Steps:
  private def nums(ns: Int*): Term[List[BigInt]] = Lift.constant(ns.toList.map(BigInt(_)))
  private val down: Term[Trouble] = Lift.constant(Trouble.Down)
  private def ok(v: Any, shelf: List[Int], time: Int) = (Right(v), shelf.map(BigInt(_)), BigInt(time))
  private def failed(e: Any, shelf: List[Int], time: Int) = (Left(e), shelf.map(BigInt(_)), BigInt(time))

  val collectAndFold = Shelved[BigInt]("collect, then fold over what it gave", Nil, ok(BigInt(18), List(1, 2, 3), 0))(
    [F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.flatMap(f.collect(nums(1, 2, 3))(x => f.as(s.put(x), x + 1)))(ys =>
        f.fold(ys, 0: Term[BigInt])((acc, y) => f.map(s.items)(held => acc + y + held.length))))

  val eachAndCondition = Shelved[BigInt]("each, then a branch by what the shelf holds", Nil, ok(BigInt(1), List(4, 5),
    0))([F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.flatMap(f.each(nums(4, 5))(s.put))(_ => f.ifM(f.map(s.items)(_.length > 1))(f.pure(1), f.pure(0))))

  val handled = Shelved[BigInt]("an error raised, given to the handler of its type", Nil, ok(BigInt(7), List(2, 9),
    0))([F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.handle[Trouble, Term[BigInt]](f.flatMap(s.put(2))(_ => f.flatMap(s.items)(held =>
        f.cond(held.length > 0)(f.raise(make[Trouble.TooBig](held.length)), f.pure(0)))))(_ =>
        f.as(s.put(9), 7)))

  val otherType = Shelved[BigInt]("an error passes a handler of another type by, to its own type's", Nil,
    ok(BigInt(2), Nil, 0))([F[_]] => (_: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.handle[Trouble, Term[BigInt]](f.handle[String, Term[BigInt]](f.raise(down))(_ => f.pure(1)))(_ => f.pure(2)))

  val unhandled = Shelved[BigInt]("an error raised and not handled: the run fails with it", Nil,
    failed(Trouble.TooBig(1), List(3), 0))([F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.flatMap(s.put(3))(_ => f.flatMap(s.items)(held => f.raise[Trouble, Term[BigInt]](
        make[Trouble.TooBig](held.length)))))

  val attempted = Shelved[Either[Trouble, BigInt]]("attempt: the error on the left, the run going on", Nil,
    ok(Left(Trouble.Down), List(1, 6), 0))([F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.flatMap(f.attempt[Trouble, BigInt](f.flatMap(s.put(1))(_ => f.raise(down))))(e => f.as(s.put(6), e)))

  val failingCall = Shelved[BigInt]("a failing model's second call fails: the first stays done", List(false, true),
    failed(Trouble.Down, List(1), 0))([F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.flatMap(s.put(1))(_ => f.flatMap(s.put(2))(_ => f.pure(3))))

  val failingHandled = Shelved[BigInt]("a failing call's error handled", List(true), ok(BigInt(0), Nil, 0))(
    [F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.handle[Trouble, Term[BigInt]](f.map(s.items)(_.length))(_ => f.pure(0)))

  val retried = Shelved[BigInt]("retry: tried again after each wait while it fails", List(true, true, false),
    ok(BigInt(5), List(5), 3))([F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.retry[Trouble, Term[BigInt]](Clock.sleep, List(1, 2))(f.as(s.put(5), 5)))

  val retriedOut = Shelved[BigInt]("retry: every try failed, the last one's error", List(true, true, true),
    failed(Trouble.Down, Nil, 3))([F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
      f.retry[Trouble, Term[BigInt]](Clock.sleep, List(1, 2))(f.as(s.put(5), 5)))

  val all: List[Shelved[?]] =
    List(collectAndFold, eachAndCondition, handled, otherType, unhandled, attempted, failingCall, failingHandled,
      retried, retriedOut)
