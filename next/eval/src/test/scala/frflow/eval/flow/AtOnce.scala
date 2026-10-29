package frflow.eval.flow

import frflow.*
import frflow.dsl.term.Lift
import frflow.eval.flow.Shelf.{held, now, putting, sleeping}

/** Programs of concurrent steps and transactions over the shelf: `parCollect` and `parCollectN`, `parTupled`, `race`,
  * `guarantee`, `bracket`, `timeout`, `atomically`. Their bodies at once only read, so any order gives one answer.
  */
object AtOnce:
  private def nums(ns: Int*): Term[List[BigInt]] = Lift.constant(ns.toList.map(BigInt(_)))
  private def ok(v: Any, shelf: List[Int], time: Int) = (Right(v), shelf.map(BigInt(_)), BigInt(time))

  val parCollectN = Shelved[List[BigInt]]("parCollectN: at most two at once, the results in order", Nil,
    ok(List(2, 3, 4).map(BigInt(_)), List(1), 0))(
      putting(1).flatMap(_ => Flow.parCollectN(2)(nums(1, 2, 3))(x => held.map(h => h.length + x))))

  val parCollect = Shelved[List[BigInt]]("parCollect: every element at once", Nil,
    ok(List(1, 2).map(BigInt(_)), Nil, 0))(Flow.parCollect(nums(1, 2))(x => held.map(h => h.length + x)))

  val parTupled = Shelved[(List[BigInt], BigInt)]("parTupled: both at once, paired", Nil,
    ok((List(BigInt(4)), BigInt(2)), List(4), 2))(
      putting(4).flatMap(_ => sleeping(2)).flatMap(_ => (held, now).parTupled))

  val raced = Shelved[List[BigInt]]("race: the winner's result", Nil, ok(List(BigInt(8)), List(8), 0))(
    putting(8).flatMap(_ => held.race(held).map(_.fold(a => a, b => b))))

  val guaranteed = Shelved[BigInt]("guarantee: the finalizer after the body's error, raised again", Nil,
    (Left(Trouble.Down), List(BigInt(1), BigInt(8)), BigInt(0)))(
      putting(1).flatMap(_ => Flow.raise[Trouble, BigInt](Lift.constant[Trouble](Trouble.Down)))
        .guarantee[Trouble](putting(8)))

  val bracketed = Shelved[BigInt]("bracket: what is acquired used, then released", Nil, ok(BigInt(1), List(1, 11), 0))(
    Flow.bracket[Trouble, BigInt, BigInt](putting(1).as(1))(n => Flow.pure(n))(n => putting(n + 10)))

  val timedOut = Shelved[Option[List[BigInt]]]("timeout: none when the program slept longer", Nil, ok(None, Nil, 2))(
    sleeping(2).flatMap(_ => held).timeout(Clock.now, 1))

  val inTime = Shelved[Option[List[BigInt]]]("timeout: the result when it took long enough", Nil,
    ok(Some(Nil), Nil, 2))(sleeping(2).flatMap(_ => held).timeout(Clock.now, 5))

  val atomic = Shelved[BigInt]("atomically: one step of the world", Nil, ok(BigInt(2), List(1, 2), 0))(
    putting(1).flatMap(_ => putting(2).flatMap(_ => held.map(_.length))).atomically)

  val all: List[Shelved[?]] = List(parCollectN, parCollect, parTupled, raced, guaranteed, bracketed, timedOut, inTime,
    atomic)
