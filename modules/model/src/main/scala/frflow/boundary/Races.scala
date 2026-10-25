package frflow
package boundary

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
