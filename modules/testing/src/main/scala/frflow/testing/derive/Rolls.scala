package frflow.testing.derive

import cats.Eval
import cats.data.{OptionT, StateT}
import scala.annotation.tailrec

/** The steps a draw is made of, each a function of where the case's draws are (`Draws`): a number from the stream,
  * one below a bound, a chance, one of several; a draw that may find nothing, and one tried again.
  */
private[derive] object Rolls:
  type O[A] = OptionT[Eval, A]
  type D[A] = StateT[O, Draws, A]

  def pure[A](a: A): D[A] = StateT.pure(a)
  def nothing[A]: D[A] = StateT.liftF(OptionT.none[Eval, A])
  def long: D[Long] = StateT(st =>
    val (s, n) = st.stream.next
    OptionT.some[Eval](st.copy(stream = s) -> n))
  def below(n: Int): D[Int] = if n <= 1 then pure(0) else long.map(x => java.lang.Math.floorMod(x, n.toLong).toInt)
  def chance(p: Double): D[Boolean] = long.map(x => (x >>> 11).toDouble / (1L << 53).toDouble < p)
  def pick[A](xs: Vector[A]): D[A] = below(xs.size).map(xs)

  def run[A](d: D[A], st: Draws): Option[(Draws, A)] = d.run(st).value.value

  /** The first, or, when it finds nothing, the second from where the first started. */
  def orElse[A](first: D[A], second: D[A]): D[A] = StateT(st => OptionT(Eval.later(run(first, st)
    .orElse(run(second, st)))))

  /** `draw` tried up to `Derive.Tries` times, each on a stream of its own, until what it draws `fits`. */
  def retried[A](draw: D[A], fits: A => Boolean): D[A] = StateT(st => OptionT(Eval.later {
    @tailrec def go(at: Draws, left: Int): Option[(Draws, A)] =
      if left == 0 then None
      else
        val (next, mine) = at.fork
        run(draw, mine).filter((_, a) => fits(a)) match
          case Some(found) => Some(found)
          case None        => go(next, left - 1)
    go(st, Derive.Tries)
  }))
