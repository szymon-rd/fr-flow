package sharing

import frflow.*
import sharing.features.Audit.makes
import sharing.domain.*
import sharing.store.LibraryStore.{libraryKept, libraryModel, libraryStarts, oneTransactionAtATime}

// What always holds of the World the service runs in (owner §45 D): the rules the branches' "at every moment" rest
// on, each kept by every program changing what it reads (`cover_`), from the state each starts in (`start_`).

/** The log: everything the library holds of a change is in it. */
val logKept = Node.claim("Everything the library holds of a change is in its log: every share was made by a request " +
    "in the log, and every waiting notice of a logged change is of an entry in the log.")(
  always(libraryModel)(lib => lib.shares.forall(s => lib.log.exists(e => makes(e, s))) &&
    lib.outbox.forall(n => n.about
      .on[Subject.Logged](e => lib.log.contains(e))
      .on[Subject.Reminder](_ => True)
      .on[Subject.Lapsed](_ => True)
      .on[Subject.Ending](_ => True))))
  .refines(auditTrail, noticesFollowChanges)
  .assuming(libraryKept, oneTransactionAtATime, libraryStarts)
