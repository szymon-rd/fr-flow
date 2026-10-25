package sharing.housekeeping

import sharing.knowledge
import sharing.domain.*

/** Tidying as plain Scala: its proven code. The job on the store runs in the server (`StoreHttp.housekeep`). */
object HousekeepingService extends Housekeeping:
  private lazy val tidyRun = knowledge.service(Housekeeping.tidyContract)()
  def tidy(library: Library, now: BigInt) = tidyRun(library, now)
