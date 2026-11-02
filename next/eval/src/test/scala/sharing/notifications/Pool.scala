package sharing.notifications

import frflow.*

/** The connections to the mail server: a pool that hands one out and takes it back, never failing. Its model counts
  * the connections in use; a run of delivery takes one and gives it back, whatever its sends do (`Flow.bracket`).
  */
object Pool:
  val take = Definition[Flow[Unit]]("a connection to the mail server taken from the pool")
  val give = Definition[Flow[Unit]]("a connection to the mail server given back to the pool")

  object poolModel extends StateModel[BigInt]("the connections to the mail server in use, as the pool counts them"):
    take.means(state.update(n => n + 1))
    give.means(state.update(n => n - 1))

  val poolKept = Node.assumption("Nothing but the service's deliveries takes connections from the pool or gives " +
      "them back.")(
    poolModel.onlyCodeChanges)

  val poolOneAtATime = Node.assumption("The pool hands out and takes back one connection at a time.")(
    poolModel.atomic)
