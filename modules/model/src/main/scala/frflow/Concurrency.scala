package frflow

/** Who wins a race, as the proofs see it: the scheduler's, so unknown. A boundary like the clock, whose model holds
  * the outcomes still to come; a proof of a flow with a `race` holds for every list of them, so for every winner.
  */
trait Races:
  /** Whether the left of a race finishes first. */
  def leftFirst: Flow[Boolean]
  /** Whether a transaction that lost a race had committed when it was cancelled (it then ran in full). */
  def committed: Flow[Boolean]

object Races:
  val boundary: Boundary[Races] = Boundary[Races]("races", "which of two flows racing finishes first, as the scheduler decides")
  private[frflow] lazy val leftFirst = classOf[Races].getMethod("leftFirst")
  private[frflow] lazy val committed = classOf[Races].getMethod("committed")

/** The races' outcomes still to come, in order: each read takes the next (the left wins, the loser had not committed,
  * when none is left). Nothing at run time reads it: a race there is run.
  */
object RacesModel extends Races, StateModel[List[Boolean]]:
  def leftFirst: Flow[Boolean] = next(true)
  def committed: Flow[Boolean] = next(false)
  private def next(otherwise: Boolean): Flow[Boolean] =
    state.get.flatMap(bs => state.set(bs.drop(1)).map(_ => bs.headOption.getOrElse(Term.lit(otherwise))))

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
