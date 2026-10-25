package frflow
package boundary

/** The races' outcomes still to come, in order: each read takes the next (the left wins, the loser had not committed,
  * when none is left). Nothing at run time reads it: a race there is run.
  */
object RacesModel extends Races, StateModel[List[Boolean]]:
  def leftFirst: Flow[Boolean] = next(true)
  def committed: Flow[Boolean] = next(false)
  private def next(otherwise: Boolean): Flow[Boolean] =
    state.get.flatMap(bs => state.set(bs.drop(1)).map(_ => bs.headOption.getOrElse(Term.lit(otherwise))))
