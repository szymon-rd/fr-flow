package sharing

import frflow.*
import sharing.audit.Audit.makes
import sharing.domain.*
import sharing.housekeeping.Housekeeping.tidy
import sharing.invitations.Invitations.{accept, invite, withdraw}
import sharing.ownership.Ownership.{owns, ownersEdit, transfer}
import sharing.requests.AccessRequests.{approve, ask, decline}
import sharing.service.Sharing
import sharing.time.Lifetimes.{gone, inForce, isOpen, isPending, reminderDue}
import sharing.time.Run.{after, events, housekeepingWithin}
import sharing.trash.Trash.{restore, trash}

// The purpose's branches, one for each part of the service, each refining the purpose: after the words they are
// stated in, before the parts' claims and the deadlines, which refine them.

/** The branch: what an invitation is. */
val invitationsAreOffers = Node.claim("An invitation is an offer from someone who may edit: only they send it or " +
    "take it back, it gives nobody access, it is taken up only by the person invited while it is open, and " +
    "housekeeping clears it away within one of its periods of its lapsing.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    (withdraw(lib, t, by, to, what) =!= lib implies mayEdit(lib, t, by, what)) &&
      forall((level: Term[Level]) =>
        (invite(lib, t, by, to, what, level) =!= lib implies mayEdit(lib, t, by, what)) &&
        forall((p: Term[PersonId], d: Term[DocumentId]) =>
          Sharing.access(invite(lib, t, by, to, what, level), t, p, d) === Sharing.access(lib, t, p, d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    accept(lib, t, p, what) =!= lib implies
      lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t))) &&
  after(events).library.invitations.forall(i => isOpen(i, after(events).now - housekeepingWithin)))
  .refines(accessFollowsShares)

/** The branch: what the trash is. */
val trashUntilGone = Node.claim("Only someone who may edit a document puts it in the trash or takes it out, and " +
    "only before it is gone; and housekeeping purges it within one of its periods of its being gone.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    (trash(lib, t, by, d) =!= lib implies mayEdit(lib, t, by, make[Target.Doc](d))) &&
      (restore(lib, t, by, d) =!= lib implies (mayEdit(lib, t, by, make[Target.Doc](d)) &&
        lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined && !gone(doc, t))))) &&
  after(events).library.documents.forall(doc => !gone(doc, after(events).now - housekeepingWithin)))
  .refines(accessFollowsShares)

/** The branch: what an access request is. */
val accessRequestsAreAsks = Node.claim("An access request is a person's ask for a document or a folder: asking " +
    "changes nothing shared, offered or kept, so it gives nobody access; only someone who may edit what it is for " +
    "answers it, and approving it, while it is pending, makes the share asked for; and housekeeping declines it " +
    "within one of its periods of its lapsing, and reminds the owners of what it is for within one of its periods " +
    "of its being due a reminder.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    ask(lib, t, p, w, level).shares === lib.shares && ask(lib, t, p, w, level).invitations === lib.invitations &&
      ask(lib, t, p, w, level).documents === lib.documents) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    (approve(lib, t, by, p, w) =!= lib implies
      (mayEdit(lib, t, by, w) && lib.requests.exists(r => r.person === p && r.what === w && isPending(r, t)))) &&
      (decline(lib, t, by, p, w) =!= lib implies mayEdit(lib, t, by, w))) &&
  after(events).library.requests.forall(r => isPending(r, after(events).now - housekeepingWithin) &&
    (r.reminded || !reminderDue(r, after(events).now - housekeepingWithin))))
  .refines(accessFollowsShares)

/** The branch: what owning a document means. */
val ownersKeepTheirDocuments = Node.claim("A document has one owner. Only its owner, while they may edit it, hands " +
    "it on, and only to someone who may edit it, who then has an edit share of it for good; and nobody unshares or " +
    "replaces an owner's shares of their own document. An owner's share is with them in person, not through a " +
    "team, so leaving a team never takes their documents from them.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    transfer(lib, t, by, d, to) =!= lib implies
      (owns(lib, by, d) && mayEdit(lib, t, by, make[Target.Doc](d)) && mayEdit(lib, t, to, make[Target.Doc](d)) &&
        owns(transfer(lib, t, by, d, to), to, d) &&
        transfer(lib, t, by, d, to).shares.contains(ownersEdit(d, to)))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    ownedBy(lib, what, withWhom) implies (Sharing.unshare(lib, t, by, what, withWhom) === lib)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    ownedBy(lib, s.what, s.withWhom) implies (Sharing.share(lib, t, by, s) === lib)))
  .refines(accessFollowsShares)

/** The branch: what housekeeping may do. */
val housekeepingClearsOnlyTheEnded = Node.claim("Housekeeping clears away only what has ended: shares no longer in " +
    "force or of a document gone, invitations no longer open, and documents gone; and what has ended stays ended, " +
    "so nothing it clears could have counted again.")(
  forall((lib: Term[Library], t: Term[BigInt]) =>
    lib.shares.forall(s => tidy(lib, t).shares.contains(s) || !inForce(s, t) ||
      lib.documents.exists(doc => gone(doc, t) && s.what === make[Target.Doc](doc.id))) &&
    lib.invitations.forall(i => tidy(lib, t).invitations.contains(i) || !isOpen(i, t)) &&
    lib.documents.forall(doc => tidy(lib, t).documents.contains(doc) || gone(doc, t))) &&
  forall((t: Term[BigInt], u: Term[BigInt]) => (t <= u) implies
    (forall((s: Term[Share]) => !inForce(s, t) implies !inForce(s, u)) &&
      forall((i: Term[Invitation]) => !isOpen(i, t) implies !isOpen(i, u)) &&
      forall((doc: Term[Document]) => gone(doc, t) implies gone(doc, u)))))
  .refines(accessFollowsShares)

/** The branch: what the log is for. */
val auditTrail = Node.claim("Every change the service makes is recorded in its log, with the request that made it " +
    "and when, in the same save as the change; so at every moment, every share the library holds was made by a " +
    "request in the log. A share is never seen before its entry is there, and every yes of canView rests on shares " +
    "whose making is logged.")(
  after(events).library.shares.forall(s => after(events).library.log.exists(e => makes(e, s))) &&
    forall((p: Term[PersonId], d: Term[DocumentId]) =>
      mayView(after(events).library, after(events).now, p, make[Target.Doc](d)) implies
        after(events).library.shares.exists(s => inForce(s, after(events).now) &&
          reaches(after(events).library, s, p) && covers(after(events).library, s, make[Target.Doc](d)) &&
          after(events).library.log.exists(e => makes(e, s)))))
  .refines(accessFollowsShares)

/** The branch: what a notice is. */
val noticesFollowChanges = Node.claim("A notice is sent only of a change already kept: at every moment, every " +
    "notice of a logged change waiting in the outbox is of an entry in the log. A notice leaves the outbox only " +
    "once the mail server has it, and the mail server has each notice once, so a person is told of each event at " +
    "least once and never twice.")(
  after(events).library.outbox.forall(n => n.about
    .on[Subject.Logged](e => after(events).library.log.contains(e))
    .on[Subject.Reminder](_ => True)
    .on[Subject.Lapsed](_ => True)
    .on[Subject.Ending](_ => True)) &&
  after(events).mailbox.forall(n => after(events).mailbox.filter(m => m === n).length === 1))
  .refines(accessFollowsShares)
