package sharing

import frflow.*
import sharing.domain.*
import sharing.features.AccessRequests.{approve, ask, decline}
import sharing.features.Housekeeping.{clearsOnlyTheEnded, tidy}
import sharing.features.Invitations.{accept, invite, openInvitation, withdraw}
import sharing.features.Ownership.transfer
import sharing.features.Sharing
import sharing.features.Trash.{restore, trash}

// Sharing's purpose, over its Declarations (may view, may edit, is in the trash): one rule a line, each the idea of
// a part below it. The access rules are parts of their own here; who may change what is said by the parts of the
// branches, in the code's words, which the claims at the bottom say the purpose's words are (`Words.scala`).

// ============================================================================
// The purpose: no clock and no durations in it
// ============================================================================

val accessFollowsShares = Node.claim("At any moment, what a person can do with a document follows the shares in " +
    "force, which change only at the hand of someone entitled to change them.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.canView(lib, t, p, d) === (!inTheTrash(lib, d) && mayView(lib, t, p, make[Target.Doc](d))) &&
      Sharing.canEdit(lib, t, p, d) === (!inTheTrash(lib, d) && allowedToEdit(lib, t, p, make[Target.Doc](d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    changes(lib, Sharing.share(lib, t, by, s)) implies allowedToEdit(lib, t, by, s.what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    changes(lib, Sharing.unshare(lib, t, by, what, withWhom)) implies allowedToEdit(lib, t, by, what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    changes(lib, Sharing.move(lib, t, by, d, into)) implies (allowedToEdit(lib, t, by, make[Target.Doc](d)) &&
      into.forall(f => allowedToEdit(lib, t, by, make[Target.InFolder](f))))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target],
      level: Term[Level]) => (changes(lib, invite(lib, t, by, to, what, level)) ||
    changes(lib, withdraw(lib, t, by, to, what))) implies allowedToEdit(lib, t, by, what)) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    changes(lib, accept(lib, t, p, what)) implies openInvitation(lib, t, p, what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    (changes(lib, trash(lib, t, by, d)) || changes(lib, restore(lib, t, by, d))) implies
      allowedToEdit(lib, t, by, make[Target.Doc](d))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    sameKept(lib, ask(lib, t, p, w, level))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    (changes(lib, approve(lib, t, by, p, w)) || changes(lib, decline(lib, t, by, p, w))) implies
      allowedToEdit(lib, t, by, w)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    changes(lib, transfer(lib, t, by, d, to)) implies allowedToEdit(lib, t, by, make[Target.Doc](d))) &&
  forall((lib: Term[Library], t: Term[BigInt]) => clearsOnlyTheEnded(lib, tidy(lib, t), t)))

// ============================================================================
// Its own parts: what the service answers, and who changes what is shared
// ============================================================================

val viewFollowsShares = Node.claim("A person can view a document exactly when it is not in the trash and a share " +
    "in force lets them view it.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.canView(lib, t, p, d) === (!inTheTrash(lib, d) && mayView(lib, t, p, make[Target.Doc](d)))))
  .refines(accessFollowsShares)

val editFollowsShares = Node.claim("A person can edit a document exactly when it is not in the trash and a share " +
    "in force lets them edit it.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.canEdit(lib, t, p, d) === (!inTheTrash(lib, d) && allowedToEdit(lib, t, p, make[Target.Doc](d)))))
  .refines(accessFollowsShares)

val onlyEditorsShare = Node.claim("Only someone who may edit a document or folder shares it.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    changes(lib, Sharing.share(lib, t, by, s)) implies mayEdit(lib, t, by, s.what)))
  .refines(accessFollowsShares)

val onlyEditorsUnshare = Node.claim("Only someone who may edit a document or folder unshares it.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    changes(lib, Sharing.unshare(lib, t, by, what, withWhom)) implies mayEdit(lib, t, by, what)))
  .refines(accessFollowsShares)

val onlyEditorsMove = Node.claim("Only someone who may edit a document, and the folder it goes into, moves it.")(
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    changes(lib, Sharing.move(lib, t, by, d, into)) implies Sharing.mayMove(lib, t, by, d, into)))
  .refines(accessFollowsShares)
