package frflow
package flow

/** `atomically` at run time, in one process: a lock on each boundary a transaction calls, taken in one order (so two
  * transactions never wait on each other), held to its end; once begun it is not cancelled. The clock and the races are
  * not locked: reading the time changes nothing.
  */
private[frflow] object Transactions:
  private val locks = new java.util.IdentityHashMap[Boundary[?], (Int, java.util.concurrent.Semaphore)]()

  private def lockOf(b: Boundary[?]): (Int, java.util.concurrent.Semaphore) = locks.synchronized {
    Option(locks.get(b)).getOrElse { val l = (locks.size, java.util.concurrent.Semaphore(1, true)); locks.put(b, l); l }
  }

  def atomically[F[_], A](boundaries: List[Boundary[?]])(fa: F[A])(using F: cats.effect.kernel.Sync[F]): F[A] =
    import cats.syntax.all.*
    import cats.effect.kernel.syntax.all.*
    val held = boundaries.filterNot(b => (b eq Clock.boundary) || (b eq Races.boundary)).distinct.map(lockOf).sortBy(_._1).map(_._2)
    F.uncancelable(_ => held.foldRight(fa)((l, inner) => F.blocking(l.acquire()) *> inner.guarantee(F.delay(l.release()))))
