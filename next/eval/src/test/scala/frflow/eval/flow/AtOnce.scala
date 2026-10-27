package frflow.eval.flow

import frflow.*
import frflow.dsl.term.Lift

/** Programs of concurrent steps and transactions over the shelf: `parCollect` and `parCollectN`, `parTupled`, `race`,
  * `guarantee`, `bracket`, `timeout`, `atomically`. Their bodies at once only read, so any order gives one answer.
  */
object AtOnce:
  private def nums(ns: Int*): Term[List[BigInt]] = Lift.constant(ns.toList.map(BigInt(_)))
  private def ok(v: Any, shelf: List[Int], time: Int) = (Right(v), shelf.map(BigInt(_)), BigInt(time))

  val parCollectN = Shelved[List[BigInt]]("parCollectN: at most two at once, the results in order", Nil,
    ok(List(2, 3, 4).map(BigInt(_)), List(1), 0))([F[_]] => (s: Shelf[F, Term], _: Clock[F, Term], f: Flow[F]) =>
      f.flatMap(s.put(1))(_ => f.parCollectN(2)(nums(1, 2, 3))(x => f.map(s.items)(h => h.length + x))))

  val parCollect = Shelved[List[BigInt]]("parCollect: every element at once", Nil,
    ok(List(1, 2).map(BigInt(_)), Nil, 0))([F[_]] => (s: Shelf[F, Term], _: Clock[F, Term], f: Flow[F]) =>
      f.parCollect(nums(1, 2))(x => f.map(s.items)(h => h.length + x)))

  val parTupled = Shelved[(List[BigInt], BigInt)]("parTupled: both at once, paired", Nil,
    ok((List(BigInt(4)), BigInt(2)), List(4), 2))([F[_]] => (s: Shelf[F, Term], c: Clock[F, Term], f: Flow[F]) =>
      f.flatMap(f.flatMap(s.put(4))(_ => c.sleep(2)))(_ => f.parTupled(s.items, c.now)))

  val raced = Shelved[List[BigInt]]("race: the winner's result", Nil, ok(List(BigInt(8)), List(8), 0))(
    [F[_]] => (s: Shelf[F, Term], _: Clock[F, Term], f: Flow[F]) =>
      f.flatMap(s.put(8))(_ => f.map(f.race(s.items, s.items))(_.fold(a => a, b => b))))

  val guaranteed = Shelved[BigInt]("guarantee: the finalizer after the body's error, raised again", Nil,
    (Left(Trouble.Down), List(BigInt(1), BigInt(8)), BigInt(0)))(
    [F[_]] => (s: Shelf[F, Term], _: Clock[F, Term], f: Flow[F]) =>
      f.guarantee[Trouble, Term[BigInt]](f.flatMap(s.put(1))(_ => f.raise(Lift.constant[Trouble](Trouble.Down))),
        s.put(8)))

  val bracketed = Shelved[BigInt]("bracket: what is acquired used, then released", Nil, ok(BigInt(1), List(1, 11), 0))(
    [F[_]] => (s: Shelf[F, Term], _: Clock[F, Term], f: Flow[F]) =>
      f.bracket[Trouble, BigInt, Term[BigInt]](f.as(s.put(1), 1))(n => f.pure(n))(n => s.put(n + 10)))

  val timedOut = Shelved[Option[List[BigInt]]]("timeout: none when the program slept longer", Nil, ok(None, Nil, 2))(
    [F[_]] => (s: Shelf[F, Term], c: Clock[F, Term], f: Flow[F]) =>
      f.timeout(c)(f.flatMap(c.sleep(2))(_ => s.items), 1))

  val inTime = Shelved[Option[List[BigInt]]]("timeout: the result when it took long enough", Nil,
    ok(Some(Nil), Nil, 2))([F[_]] => (s: Shelf[F, Term], c: Clock[F, Term], f: Flow[F]) =>
      f.timeout(c)(f.flatMap(c.sleep(2))(_ => s.items), 5))

  val atomic = Shelved[BigInt]("atomically: one step of the world", Nil, ok(BigInt(2), List(1, 2), 0))(
    [F[_]] => (s: Shelf[F, Term], _: Clock[F, Term], f: Flow[F]) =>
      f.atomically(f.flatMap(s.put(1))(_ => f.flatMap(s.put(2))(_ => f.map(s.items)(_.length)))))

  val all: List[Shelved[?]] = List(parCollectN, parCollect, parTupled, raced, guaranteed, bracketed, timedOut, inTime,
    atomic)
