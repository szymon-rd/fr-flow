package sharing

import frflow.*
import sharing.features.Audit.{logged, noticeLogged}
import sharing.store.LibraryStore.{libraryKept, libraryModel, libraryStarts, oneTransactionAtATime}

// What always holds of the World the service runs in (owner §45 D): the rules the branches' "at every moment" rest
// on, each kept by every program changing what it reads (`cover_`), from the state each starts in (`start_`).

/** The log's account of the shares: what auditTrail reads at every moment. */
val sharesLogged = Node.claim("Every share the library holds was made by a request in its log.")(
  always(libraryModel)(lib => lib.shares.forall(s => logged(lib, s))))
  .refines(auditTrail)
  .assuming(libraryKept, oneTransactionAtATime, libraryStarts)

/** The log's account of the notices: what noticesFollowChanges reads at every moment. */
val noticesLogged = Node.claim("Every waiting notice of a logged change is of an entry in the log.")(
  always(libraryModel)(lib => lib.outbox.forall(n => noticeLogged(lib, n))))
  .refines(noticesFollowChanges)
  .assuming(libraryKept, oneTransactionAtATime, libraryStarts)
