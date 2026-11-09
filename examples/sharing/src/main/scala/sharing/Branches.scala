package sharing

import frflow.*
import sharing.domain.*
import sharing.features.AccessRequests.{approve, ask, decline, pendingRequest}
import sharing.features.Invitations.{accept, invite, openInvitation, withdraw}
import sharing.features.Sharing.sameAccess
import sharing.features.Trash.{restorable, restore, trash}
import sharing.store.LibraryStore.libraryModel
import sharing.time.ClockKept.clockModel
import sharing.time.Lifetimes.{gone, isOpen, isPending, reminderDue}
import sharing.time.Run.housekeepingWithin

// The purpose's branches about what people ask of each other, each refining the purpose: a parent stating the idea,
// one line per idea of its parts, then the parts. Each timeless idea is a smaller statement here; each line about the
// World as it stands is the idea of a deadline (`Deadlines.scala`), read through the lifetimes' words.

/** The branch: what an invitation is. */
val invitationsAreOffers = Node.claim("An invitation is an offer from someone who may edit, which gives nobody " +
    "access until the person invited takes it up, and which housekeeping clears within one period of its lapsing.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target],
      level: Term[Level]) =>
    ((changes(lib, invite(lib, t, by, to, what, level)) || changes(lib, withdraw(lib, t, by, to, what))) implies
      mayEdit(lib, t, by, what)) &&
    sameAccess(lib, invite(lib, t, by, to, what, level), t) &&
    (changes(lib, accept(lib, t, to, what)) implies openInvitation(lib, t, to, what))) &&
  libraryModel.current.invitations.forall(i => isOpen(i, clockModel.current - housekeepingWithin)))
  .refines(accessFollowsShares)

val onlyEditorsInvite = Node.claim("Only someone who may edit a document or folder invites a person to it or " +
    "withdraws their invitation.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target],
      level: Term[Level]) =>
    (changes(lib, invite(lib, t, by, to, what, level)) || changes(lib, withdraw(lib, t, by, to, what))) implies
      mayEdit(lib, t, by, what)))
  .refines(invitationsAreOffers)

val invitingGivesNoAccess = Node.claim("Inviting someone changes nobody's access to any document.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target],
      level: Term[Level]) => sameAccess(lib, invite(lib, t, by, to, what, level), t)))
  .refines(invitationsAreOffers)

val onlyTheInvitedAccept = Node.claim("An invitation is taken up only by the person invited, while it is open.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    changes(lib, accept(lib, t, p, what)) implies openInvitation(lib, t, p, what)))
  .refines(invitationsAreOffers)

/** The branch: what the trash is. */
val trashUntilGone = Node.claim("A document is put in the trash or taken out only by someone who may edit it, " +
    "only before it is gone, and housekeeping purges it within one period of its being gone.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    ((changes(lib, trash(lib, t, by, d)) || changes(lib, restore(lib, t, by, d))) implies
      mayEdit(lib, t, by, make[Target.Doc](d))) &&
    (changes(lib, restore(lib, t, by, d)) implies restorable(lib, t, d))) &&
  libraryModel.current.documents.forall(doc => !gone(doc, clockModel.current - housekeepingWithin)))
  .refines(accessFollowsShares)

val onlyEditorsTrash = Node.claim("Only someone who may edit a document puts it in the trash or takes it out.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    (changes(lib, trash(lib, t, by, d)) || changes(lib, restore(lib, t, by, d))) implies
      mayEdit(lib, t, by, make[Target.Doc](d))))
  .refines(trashUntilGone)

val restoredOnlyBeforeGone = Node.claim("A document is taken out of the trash only before it is gone.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    changes(lib, restore(lib, t, by, d)) implies restorable(lib, t, d)))
  .refines(trashUntilGone)

/** The branch: what an access request is. */
val accessRequestsAreAsks = Node.claim("An access request is a person's ask, which changes nothing shared until " +
    "someone who may edit approves it while it is pending, and which housekeeping answers within one period.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    sameKept(lib, ask(lib, t, p, w, level))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    ((changes(lib, approve(lib, t, by, p, w)) || changes(lib, decline(lib, t, by, p, w))) implies
      mayEdit(lib, t, by, w)) &&
    (changes(lib, approve(lib, t, by, p, w)) implies pendingRequest(lib, t, p, w))) &&
  libraryModel.current.requests.forall(r => isPending(r, clockModel.current - housekeepingWithin)) &&
  libraryModel.current.requests.forall(r => r.reminded || !reminderDue(r, clockModel.current - housekeepingWithin)))
  .refines(accessFollowsShares)

val askingChangesNothingKept = Node.claim("Asking for access changes nothing shared, offered or kept.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    sameKept(lib, ask(lib, t, p, w, level))))
  .refines(accessRequestsAreAsks)

val onlyEditorsAnswer = Node.claim("Only someone who may edit a document or folder approves or declines a request " +
    "for it.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    (changes(lib, approve(lib, t, by, p, w)) || changes(lib, decline(lib, t, by, p, w))) implies
      mayEdit(lib, t, by, w)))
  .refines(accessRequestsAreAsks)

val approvedOnlyWhilePending = Node.claim("A request is approved only while it is pending.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    changes(lib, approve(lib, t, by, p, w)) implies pendingRequest(lib, t, p, w)))
  .refines(accessRequestsAreAsks)
