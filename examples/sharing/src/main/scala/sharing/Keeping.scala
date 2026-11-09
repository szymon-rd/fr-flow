package sharing

import frflow.*
import sharing.domain.*
import sharing.features.Audit.{letsView, logged, noticeLogged}
import sharing.features.Housekeeping.{clearsOnlyTheEnded, tidy}
import sharing.features.Ownership.{mayHandOn, ownsForGood, transfer}
import sharing.features.Sharing
import sharing.notifications.Mailer.taken
import sharing.store.LibraryStore.libraryModel
import sharing.time.ClockKept.clockModel

// The purpose's branches about what the service keeps, each refining the purpose: a parent stating the idea, one
// line per idea of its parts, then the parts. A line about the World as it stands is the idea of a rule of the
// World (`Kept.scala`) at this moment.

/** The branch: what owning a document means. */
val ownersKeepTheirDocuments = Node.claim("A document stays with its owner until they hand it on, and nobody takes " +
    "an owner's own share of it away.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    (changes(lib, transfer(lib, t, by, d, to)) implies mayHandOn(lib, t, by, d, to)) &&
    (changes(lib, transfer(lib, t, by, d, to)) implies ownsForGood(transfer(lib, t, by, d, to), to, d))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    ownedBy(lib, what, withWhom) implies (Sharing.unshare(lib, t, by, what, withWhom) === lib)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    ownedBy(lib, s.what, s.withWhom) implies (Sharing.share(lib, t, by, s) === lib)))
  .refines(accessFollowsShares)

val onlyTheOwnerHandsOn = Node.claim("A document is handed on only by its owner, while they may edit it, to " +
    "someone who may edit it.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    changes(lib, transfer(lib, t, by, d, to)) implies mayHandOn(lib, t, by, d, to)))
  .refines(ownersKeepTheirDocuments)

val newOwnerOwnsForGood = Node.claim("A document handed on is owned by the person it went to, with an edit share " +
    "of it for good.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    changes(lib, transfer(lib, t, by, d, to)) implies ownsForGood(transfer(lib, t, by, d, to), to, d)))
  .refines(ownersKeepTheirDocuments)

val nobodyUnsharesAnOwner = Node.claim("Nobody unshares an owner's share of their own document.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    ownedBy(lib, what, withWhom) implies (Sharing.unshare(lib, t, by, what, withWhom) === lib)))
  .refines(ownersKeepTheirDocuments)

val nobodyReplacesAnOwner = Node.claim("Nobody replaces an owner's share of their own document.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    ownedBy(lib, s.what, s.withWhom) implies (Sharing.share(lib, t, by, s) === lib)))
  .refines(ownersKeepTheirDocuments)

/** The branch: what housekeeping may do. */
val housekeepingClearsOnlyTheEnded = Node.claim("Housekeeping clears away only what has ended.")(
  forall((lib: Term[Library], t: Term[BigInt]) => clearsOnlyTheEnded(lib, tidy(lib, t), t)))
  .refines(accessFollowsShares)

/** The branch: what the log is for. */
val auditTrail = Node.claim("At every moment, every share the library holds, and so every yes of viewing, is " +
    "explained by a request in its log.")(
  libraryModel.current.shares.forall(s => logged(libraryModel.current, s)) &&
  forall((p: Term[PersonId], d: Term[DocumentId]) =>
    mayView(libraryModel.current, clockModel.current, p, make[Target.Doc](d)) implies
      libraryModel.current.shares.exists(s =>
        letsView(libraryModel.current, clockModel.current, s, p, make[Target.Doc](d)) &&
          logged(libraryModel.current, s))))
  .refines(accessFollowsShares)

val viewingRestsOnTheLog = Node.claim("Every yes of viewing rests on a share whose making is in the log.")(
  forall((p: Term[PersonId], d: Term[DocumentId]) =>
    mayView(libraryModel.current, clockModel.current, p, make[Target.Doc](d)) implies
      libraryModel.current.shares.exists(s =>
        letsView(libraryModel.current, clockModel.current, s, p, make[Target.Doc](d)) &&
          logged(libraryModel.current, s))))
  .refines(auditTrail)

/** The branch: what a notice is. */
/** Its second line is its own: a claim of `taken` alone has no code FrFlow checks it against (the define is reached
  * only through the mail server's model), so the step proves it here.
  */
val noticesFollowChanges = Node.claim("A person is told of each change already kept, and the mail server has " +
    "each notice once.")(
  libraryModel.current.outbox.forall(n => noticeLogged(libraryModel.current, n)) &&
  forall((ns: Term[List[Notice]], n: Term[Notice]) =>
    taken(ns, n).contains(n) && (ns.contains(n) implies (taken(ns, n) === ns))))
  .refines(accessFollowsShares)
