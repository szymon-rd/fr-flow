import FrFlowGen.Old.Domain.Def_AccessRequests.approveCode
import FrFlowGen.Old.Domain.Def_AccessRequests.askCode
import FrFlowGen.Old.Domain.Def_AccessRequests.chaseCode
import FrFlowGen.Old.Domain.Def_AccessRequests.chaseNotices
import FrFlowGen.Old.Domain.Def_AccessRequests.chased
import FrFlowGen.Old.Domain.Def_AccessRequests.declineCode
import FrFlowGen.Old.Domain.Def_AccessRequests.holds
import FrFlowGen.Old.Domain.Def_AccessRequests.isFor
import FrFlowGen.Old.Domain.Def_AccessRequests.requestsWithout
import FrFlowGen.Old.Domain.Def_Audit.explains
import FrFlowGen.Old.Domain.Def_Audit.forgetCode
import FrFlowGen.Old.Domain.Def_Audit.makes
import FrFlowGen.Old.Domain.Def_Audit.recordCode
import FrFlowGen.Old.Domain.Def_Housekeeping.ofGone
import FrFlowGen.Old.Domain.Def_Housekeeping.tidyCode
import FrFlowGen.Old.Domain.Def_Invitations.acceptCode
import FrFlowGen.Old.Domain.Def_Invitations.invitationsWithout
import FrFlowGen.Old.Domain.Def_Invitations.inviteCode
import FrFlowGen.Old.Domain.Def_Invitations.withdrawCode
import FrFlowGen.Old.Domain.Def_Lifetimes.goneCode
import FrFlowGen.Old.Domain.Def_Lifetimes.inForceCode
import FrFlowGen.Old.Domain.Def_Lifetimes.isOpenCode
import FrFlowGen.Old.Domain.Def_Lifetimes.isPendingCode
import FrFlowGen.Old.Domain.Def_Lifetimes.reminderDueCode
import FrFlowGen.Old.Domain.Def_Notifications.announceCode
import FrFlowGen.Old.Domain.Def_Notifications.endingNotices
import FrFlowGen.Old.Domain.Def_Notifications.endsInADay
import FrFlowGen.Old.Domain.Def_Notifications.firstOfEach
import FrFlowGen.Old.Domain.Def_Notifications.mailbox
import FrFlowGen.Old.Domain.Def_Notifications.noticesOf
import FrFlowGen.Old.Domain.Def_Notifications.reachedBy
import FrFlowGen.Old.Domain.Def_Notifications.taken
import FrFlowGen.Old.Domain.Def_Notifications.warnCode
import FrFlowGen.Old.Domain.Def_Ownership.owns
import FrFlowGen.Old.Domain.Def_Ownership.transferCode
import FrFlowGen.Old.Domain.Def_Run.answered
import FrFlowGen.Old.Domain.Def_Run.housekept
import FrFlowGen.Old.Domain.Def_Run.served
import FrFlowGen.Old.Domain.Def_Run.step
import FrFlowGen.Old.Domain.Def_Sharing.accessCode
import FrFlowGen.Old.Domain.Def_Sharing.canEditCode
import FrFlowGen.Old.Domain.Def_Sharing.canViewCode
import FrFlowGen.Old.Domain.Def_Sharing.foldersAt
import FrFlowGen.Old.Domain.Def_Sharing.granteesOf
import FrFlowGen.Old.Domain.Def_Sharing.mayMove
import FrFlowGen.Old.Domain.Def_Sharing.moveCode
import FrFlowGen.Old.Domain.Def_Sharing.placesOf
import FrFlowGen.Old.Domain.Def_Sharing.shareCode
import FrFlowGen.Old.Domain.Def_Sharing.sharesWithout
import FrFlowGen.Old.Domain.Def_Sharing.strongest
import FrFlowGen.Old.Domain.Def_Sharing.unshareCode
import FrFlowGen.Old.Domain.Def_SharingHttp.afterRequest
import FrFlowGen.Old.Domain.Def_SharingHttp.answerTo
import FrFlowGen.Old.Domain.Def_SharingHttp.served
import FrFlowGen.Old.Domain.Def_Trash.mayRestore
import FrFlowGen.Old.Domain.Def_Trash.restoreCode
import FrFlowGen.Old.Domain.Def_Trash.trashCode
import FrFlowGen.Sharing.Domain.Def_acceptCode
import FrFlowGen.Sharing.Domain.Def_accessCode
import FrFlowGen.Sharing.Domain.Def_afterRequest
import FrFlowGen.Sharing.Domain.Def_announceCode
import FrFlowGen.Sharing.Domain.Def_answerTo
import FrFlowGen.Sharing.Domain.Def_answered
import FrFlowGen.Sharing.Domain.Def_approveCode
import FrFlowGen.Sharing.Domain.Def_askCode
import FrFlowGen.Sharing.Domain.Def_canEditCode
import FrFlowGen.Sharing.Domain.Def_canViewCode
import FrFlowGen.Sharing.Domain.Def_chaseCode
import FrFlowGen.Sharing.Domain.Def_chaseNotices
import FrFlowGen.Sharing.Domain.Def_chased
import FrFlowGen.Sharing.Domain.Def_declineCode
import FrFlowGen.Sharing.Domain.Def_endingNotices
import FrFlowGen.Sharing.Domain.Def_endsInADay
import FrFlowGen.Sharing.Domain.Def_explains
import FrFlowGen.Sharing.Domain.Def_firstOfEach
import FrFlowGen.Sharing.Domain.Def_foldersAt
import FrFlowGen.Sharing.Domain.Def_forgetCode
import FrFlowGen.Sharing.Domain.Def_goneCode
import FrFlowGen.Sharing.Domain.Def_granteesOf
import FrFlowGen.Sharing.Domain.Def_holds
import FrFlowGen.Sharing.Domain.Def_housekept
import FrFlowGen.Sharing.Domain.Def_inForceCode
import FrFlowGen.Sharing.Domain.Def_invitationsWithout
import FrFlowGen.Sharing.Domain.Def_inviteCode
import FrFlowGen.Sharing.Domain.Def_isFor
import FrFlowGen.Sharing.Domain.Def_isOpenCode
import FrFlowGen.Sharing.Domain.Def_isPendingCode
import FrFlowGen.Sharing.Domain.Def_mailbox
import FrFlowGen.Sharing.Domain.Def_makes
import FrFlowGen.Sharing.Domain.Def_mayMove
import FrFlowGen.Sharing.Domain.Def_mayRestore
import FrFlowGen.Sharing.Domain.Def_moveCode
import FrFlowGen.Sharing.Domain.Def_noticesOf
import FrFlowGen.Sharing.Domain.Def_ofGone
import FrFlowGen.Sharing.Domain.Def_owns
import FrFlowGen.Sharing.Domain.Def_placesOf
import FrFlowGen.Sharing.Domain.Def_reachedBy
import FrFlowGen.Sharing.Domain.Def_recordCode
import FrFlowGen.Sharing.Domain.Def_reminderDueCode
import FrFlowGen.Sharing.Domain.Def_requestsWithout
import FrFlowGen.Sharing.Domain.Def_restoreCode
import FrFlowGen.Sharing.Domain.Def_served
import FrFlowGen.Sharing.Domain.Def_shareCode
import FrFlowGen.Sharing.Domain.Def_sharesWithout
import FrFlowGen.Sharing.Domain.Def_step
import FrFlowGen.Sharing.Domain.Def_strongest
import FrFlowGen.Sharing.Domain.Def_taken
import FrFlowGen.Sharing.Domain.Def_tidyCode
import FrFlowGen.Sharing.Domain.Def_transferCode
import FrFlowGen.Sharing.Domain.Def_trashCode
import FrFlowGen.Sharing.Domain.Def_unshareCode
import FrFlowGen.Sharing.Domain.Def_warnCode
import FrFlowGen.Sharing.Domain.Def_withdrawCode
import FrFlowGen.Old.AcceptContract.Spec
import FrFlowGen.Sharing.acceptContract.Spec
import FrFlowGen.Old.AccessContract.Spec
import FrFlowGen.Sharing.accessContract.Spec
import FrFlowGen.Old.AnnounceContract.Spec
import FrFlowGen.Sharing.announceContract.Spec
import FrFlowGen.Old.ApproveContract.Spec
import FrFlowGen.Sharing.approveContract.Spec
import FrFlowGen.Old.AskContract.Spec
import FrFlowGen.Sharing.askContract.Spec
import FrFlowGen.Old.ChaseContract.Spec
import FrFlowGen.Sharing.chaseContract.Spec
import FrFlowGen.Old.ClockNeverGoesBack.Spec
import FrFlowGen.Sharing.clockNeverGoesBack.Spec
import FrFlowGen.Old.DeclineContract.Spec
import FrFlowGen.Sharing.declineContract.Spec
import FrFlowGen.Old.ForgetContract.Spec
import FrFlowGen.Sharing.forgetContract.Spec
import FrFlowGen.Old.HousekeepingClearsOnlyTheEnded.Spec
import FrFlowGen.Sharing.housekeepingClearsOnlyTheEnded.Spec
import FrFlowGen.Old.InviteContract.Spec
import FrFlowGen.Sharing.inviteContract.Spec
import FrFlowGen.Old.MoveContract.Spec
import FrFlowGen.Sharing.moveContract.Spec
import FrFlowGen.Old.OwnersKeepTheirDocuments.Spec
import FrFlowGen.Sharing.ownersKeepTheirDocuments.Spec
import FrFlowGen.Old.RecordContract.Spec
import FrFlowGen.Sharing.recordContract.Spec
import FrFlowGen.Old.RestoreContract.Spec
import FrFlowGen.Sharing.restoreContract.Spec
import FrFlowGen.Old.ShareContract.Spec
import FrFlowGen.Sharing.shareContract.Spec
import FrFlowGen.Old.TidyContract.Spec
import FrFlowGen.Sharing.tidyContract.Spec
import FrFlowGen.Old.TransferContract.Spec
import FrFlowGen.Sharing.transferContract.Spec
import FrFlowGen.Old.TrashContract.Spec
import FrFlowGen.Sharing.trashContract.Spec
import FrFlowGen.Old.UnshareContract.Spec
import FrFlowGen.Sharing.unshareContract.Spec
import FrFlowGen.Old.WarnContract.Spec
import FrFlowGen.Sharing.warnContract.Spec
import FrFlowGen.Old.WithdrawContract.Spec
import FrFlowGen.Sharing.withdrawContract.Spec
import FrFlowGen.Old.CanViewContract.Spec
import FrFlowGen.Old.CanEditContract.Spec
import FrFlowGen.Old.InForceContract.Spec
import FrFlowGen.Old.IsOpenContract.Spec
import FrFlowGen.Old.GoneContract.Spec
import FrFlowGen.Old.PendingContract.Spec
import FrFlowGen.Old.ReminderDueContract.Spec
import FrFlowGen.Sharing.canViewContract.Spec
import FrFlowGen.Sharing.canEditContract.Spec
import FrFlowGen.Sharing.inForceContract.Spec
import FrFlowGen.Sharing.isOpenContract.Spec
import FrFlowGen.Sharing.goneContract.Spec
import FrFlowGen.Sharing.pendingContract.Spec
import FrFlowGen.Sharing.reminderDueContract.Spec
import FrFlowGen.Old.Domain.Term_reaches
import FrFlowGen.Old.Domain.Term_covers
import FrFlowGen.Old.Domain.Term_mayView
import FrFlowGen.Old.Domain.Term_mayEdit
import FrFlowGen.Old.Domain.Term_inTrash
import FrFlowGen.Old.Domain.Term_ownedBy
import FrFlowGen.Old.Domain.Term_invitationLasts
import FrFlowGen.Old.Domain.Term_trashKeeps
import FrFlowGen.Old.Domain.Term_requestLasts
import FrFlowGen.Old.Domain.Term_remindAfter
import FrFlowGen.Old.Domain.Term_housekeepingWithin
import FrFlowGen.Sharing.reach.Spec
import FrFlowGen.Sharing.cover.Spec
import FrFlowGen.Sharing.permission.Spec
import FrFlowGen.Sharing.editPermission.Spec
import FrFlowGen.Sharing.whoMayEdit.Spec
import FrFlowGen.Sharing.inTrash.Spec
import FrFlowGen.Sharing.whatIsTrashed.Spec
import FrFlowGen.Sharing.ownersShare.Spec
import FrFlowGen.Sharing.invitationLifetime.Spec
import FrFlowGen.Sharing.trashLifetime.Spec
import FrFlowGen.Sharing.requestLifetime.Spec
import FrFlowGen.Sharing.reminderTime.Spec
import FrFlowGen.Sharing.housekeepingPeriod.Spec

/-! Sharing's statements as today's library stated them (`reference/sharing`, in namespace `Old` over the port's
types), against the port's (ARCHITECTURE section 9, equivalence 4). Today's defines are the port's (`PortEq`): most are
the same terms; those whose Lean differs in form (an option's fold read as a match or as a quantifier, a match's arms
in another order, a request granted through a helper) are proven equal. Each of today's contracts, and each claim
today stated over the same Definitions, is proven equivalent to the port's, for every meaning of what it speaks of.
Today's words were defines, not nodes: each meets the claim the port states of its word (`_today`). The rest are
listed in `Judged.unstated`, each with why it is not stated here: today's purpose's module, today's three programs and
today's branches and deadlines read today's programs over today's boundaries' world (`Boundaries.lean`, its clock a
record of its own), which the port's types do not have. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace PortEq

theorem askCode_eq : @Old.AccessRequests.askCode = @Sharing.askCode := rfl
theorem chaseCode_eq : @Old.AccessRequests.chaseCode = @Sharing.chaseCode := rfl
theorem chaseNotices_eq : @Old.AccessRequests.chaseNotices = @Sharing.chaseNotices := rfl
theorem chased_eq : @Old.AccessRequests.chased = @Sharing.chased := rfl
theorem declineCode_eq : @Old.AccessRequests.declineCode = @Sharing.declineCode := rfl
theorem holds_eq : @Old.AccessRequests.holds = @Sharing.holds := rfl
theorem isFor_eq : @Old.AccessRequests.isFor = @Sharing.isFor := rfl
theorem requestsWithout_eq : @Old.AccessRequests.requestsWithout = @Sharing.requestsWithout := rfl
theorem recordCode_eq : @Old.Audit.recordCode = @Sharing.recordCode := rfl
theorem ofGone_eq : @Old.Housekeeping.ofGone = @Sharing.ofGone := rfl
theorem tidyCode_eq : @Old.Housekeeping.tidyCode = @Sharing.tidyCode := rfl
theorem invitationsWithout_eq : @Old.Invitations.invitationsWithout = @Sharing.invitationsWithout := rfl
theorem inviteCode_eq : @Old.Invitations.inviteCode = @Sharing.inviteCode := rfl
theorem withdrawCode_eq : @Old.Invitations.withdrawCode = @Sharing.withdrawCode := rfl
theorem isOpenCode_eq : @Old.Lifetimes.isOpenCode = @Sharing.isOpenCode := rfl
theorem isPendingCode_eq : @Old.Lifetimes.isPendingCode = @Sharing.isPendingCode := rfl
theorem reminderDueCode_eq : @Old.Lifetimes.reminderDueCode = @Sharing.reminderDueCode := rfl
theorem announceCode_eq : @Old.Notifications.announceCode = @Sharing.announceCode := rfl
theorem endingNotices_eq : @Old.Notifications.endingNotices = @Sharing.endingNotices := rfl
theorem endsInADay_eq : @Old.Notifications.endsInADay = @Sharing.endsInADay := rfl
theorem firstOfEach_eq : @Old.Notifications.firstOfEach = @Sharing.firstOfEach := rfl
theorem mailbox_eq : @Old.Notifications.mailbox = @Sharing.mailbox := rfl
theorem noticesOf_eq : @Old.Notifications.noticesOf = @Sharing.noticesOf := rfl
theorem reachedBy_eq : @Old.Notifications.reachedBy = @Sharing.reachedBy := rfl
theorem taken_eq : @Old.Notifications.taken = @Sharing.taken := rfl
theorem warnCode_eq : @Old.Notifications.warnCode = @Sharing.warnCode := rfl
theorem accessCode_eq : @Old.Old.accessCode = @Sharing.accessCode := rfl
theorem canEditCode_eq : @Old.Old.canEditCode = @Sharing.canEditCode := rfl
theorem canViewCode_eq : @Old.Old.canViewCode = @Sharing.canViewCode := rfl
theorem granteesOf_eq : @Old.Old.granteesOf = @Sharing.granteesOf := rfl
theorem placesOf_eq : @Old.Old.placesOf = @Sharing.placesOf := rfl
theorem shareCode_eq : @Old.Old.shareCode = @Sharing.shareCode := rfl
theorem sharesWithout_eq : @Old.Old.sharesWithout = @Sharing.sharesWithout := rfl
theorem strongest_eq : @Old.Old.strongest = @Sharing.strongest := rfl
theorem unshareCode_eq : @Old.Old.unshareCode = @Sharing.unshareCode := rfl
theorem owns_eq : @Old.Ownership.owns = @Sharing.owns := rfl
theorem transferCode_eq : @Old.Ownership.transferCode = @Sharing.transferCode := rfl
theorem mayRestore_eq : @Old.Trash.mayRestore = @Sharing.mayRestore := rfl
theorem restoreCode_eq : @Old.Trash.restoreCode = @Sharing.restoreCode := rfl
theorem trashCode_eq : @Old.Trash.trashCode = @Sharing.trashCode := rfl

theorem inForceCode_eq : @Old.Lifetimes.inForceCode = @Sharing.inForceCode := by
  funext s t; apply propext
  simp only [Old.Lifetimes.inForceCode, Sharing.inForceCode]
  cases s.«until» <;> simp

theorem goneCode_eq : @Old.Lifetimes.goneCode = @Sharing.goneCode := by
  funext k d t; apply propext
  simp only [Old.Lifetimes.goneCode, Sharing.goneCode]
  cases d.trashed <;> simp

theorem mayMove_eq : @Old.Old.mayMove = @Sharing.mayMove := by
  funext me lib t b d into; apply propext
  simp only [Old.Old.mayMove, Sharing.mayMove]
  cases into <;> simp

theorem foldersAt_eq : @Old.Old.foldersAt = @Sharing.foldersAt := by
  funext lib into
  cases into <;> simp only [Old.Old.foldersAt, Sharing.foldersAt]
  split <;> rename_i h <;> simp [h]

theorem acceptCode_eq : @Old.Invitations.acceptCode = @Sharing.acceptCode := by
  funext io ob lib t p what
  simp only [Old.Invitations.acceptCode, Sharing.acceptCode, sharesWithout_eq, invitationsWithout_eq]
  split <;> rename_i h <;> simp only [h]

theorem moveCode_eq : @Old.Old.moveCode = @Sharing.moveCode := by
  funext me lib t b d into
  simp only [Old.Old.moveCode, Sharing.moveCode, mayMove_eq, foldersAt_eq]

theorem makes_eq : @Old.Audit.makes = @Sharing.makes := by
  funext e s
  rcases e with ⟨i, a, c⟩
  cases c with
  | Made r => cases r <;> simp [Old.Audit.makes, Sharing.makes, Sharing.madeBy]
  | _ => rfl

theorem explains_eq : @Old.Audit.explains = @Sharing.explains := by
  funext lib e
  simp only [Old.Audit.explains, Sharing.explains, makes_eq]

theorem forgetCode_eq : @Old.Audit.forgetCode = @Sharing.forgetCode := by
  funext lib t
  simp only [Old.Audit.forgetCode, Sharing.forgetCode, explains_eq]

theorem approveCode_eq : @Old.AccessRequests.approveCode = @Sharing.approveCode := by
  funext ip me ob lib t b p w
  simp only [Old.AccessRequests.approveCode, Sharing.approveCode, Sharing.granted, sharesWithout_eq,
    requestsWithout_eq]
  split
  · rename_i r h
    have hr := List.find?_some h
    simp only [decide_eq_true_eq] at hr
    obtain ⟨⟨hp, hw⟩, _⟩ := hr
    subst hp; subst hw
    simp only [h]
  · rename_i h; simp only [h]

theorem answered_eq : @Old.Run.answered = @Sharing.answered := by
  funext me ob io gn ip lib t r
  cases r <;> simp only [Old.Run.answered, Sharing.answered, shareCode_eq, unshareCode_eq, moveCode_eq,
    inviteCode_eq, acceptCode_eq, withdrawCode_eq, trashCode_eq, restoreCode_eq, askCode_eq, approveCode_eq,
    declineCode_eq, transferCode_eq]

theorem answerTo_eq : @Old.SharingHttp.answerTo = @Sharing.answerTo := by
  funext ac me ob io ip gn lib t r
  cases r <;> simp only [Old.SharingHttp.answerTo, Sharing.answerTo, mayMove_eq, mayRestore_eq, owns_eq] <;>
    first | rfl | congr 1

end PortEq

namespace Port
open Sharing


theorem canView_eq (access : Library → Int → PersonId → DocumentId → Option Level)
    (canView : Library → Int → PersonId → DocumentId → Prop) :
    Old.CanViewContract.claim access canView ↔ Sharing.canViewContract.claim canView access := by
  simp only [Old.CanViewContract.claim, Old.CanViewContract.post, Sharing.canViewContract.claim]

theorem canEdit_eq (access : Library → Int → PersonId → DocumentId → Option Level)
    (canEdit : Library → Int → PersonId → DocumentId → Prop) :
    Old.CanEditContract.claim access canEdit ↔ Sharing.canEditContract.claim canEdit access := by
  simp only [Old.CanEditContract.claim, Old.CanEditContract.post, Sharing.canEditContract.claim]

theorem inForce_eq (inForce : Share → Int → Prop) :
    Old.InForceContract.claim inForce ↔ Sharing.inForceContract.claim inForce := by
  simp only [Old.InForceContract.claim, Old.InForceContract.post, Sharing.inForceContract.claim]
  constructor <;> intro h s t <;> rw [h s t] <;> cases s.«until» <;> simp

theorem isOpen_eq (lasts : Int) (isOpen : Invitation → Int → Prop) :
    Old.IsOpenContract.claim lasts isOpen ↔ Sharing.isOpenContract.claim isOpen lasts := by
  simp only [Old.IsOpenContract.claim, Old.IsOpenContract.post, Sharing.isOpenContract.claim]

theorem gone_eq (keeps : Int) (gone : Document → Int → Prop) :
    Old.GoneContract.claim keeps gone ↔ Sharing.goneContract.claim gone keeps := by
  simp only [Old.GoneContract.claim, Old.GoneContract.post, Sharing.goneContract.claim]
  constructor <;> intro h d t <;> rw [h d t] <;> cases d.trashed <;> simp

theorem pending_eq (lasts : Int) (isPending : AccessRequest → Int → Prop) :
    Old.PendingContract.claim lasts isPending ↔ Sharing.pendingContract.claim isPending lasts := by
  simp only [Old.PendingContract.claim, Old.PendingContract.post, Sharing.pendingContract.claim]

theorem reminderDue_eq (after : Int) (reminderDue : AccessRequest → Int → Prop) :
    Old.ReminderDueContract.claim after reminderDue ↔ Sharing.reminderDueContract.claim reminderDue after := by
  simp only [Old.ReminderDueContract.claim, Old.ReminderDueContract.post, Sharing.reminderDueContract.claim]



theorem acceptContract_eq (accept : Library → Int → PersonId → Target → Library) (isOpen : Invitation → Int → Prop) (ownedBy : Library → Target → Grantee → Prop) :
    Old.AcceptContract.claim isOpen ownedBy accept ↔ Sharing.acceptContract.claim accept isOpen ownedBy := by
  simp only [Old.AcceptContract.claim, Sharing.acceptContract.claim, Old.AcceptContract.post,
    PortEq.sharesWithout_eq, PortEq.invitationsWithout_eq]
  constructor <;> intro h lib t p w <;> rw [h] <;>
    cases hf : List.find? (fun i => decide ((i.to = p ∧ i.what = w) ∧ isOpen i t)) lib.invitations <;>
    simp only [hf] <;> rfl

theorem accessContract_eq (access : Library → Int → PersonId → DocumentId → (Option Level)) (inTrash : Library → DocumentId → Prop) (inForce : Share → Int → Prop) :
    Old.AccessContract.claim inTrash inForce access ↔ Sharing.accessContract.claim access inTrash inForce := by
  simp only [Old.AccessContract.claim, Sharing.accessContract.claim, Old.AccessContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem announceContract_eq (announce : Library → Library → Request → Entry → Library) :
    Old.AnnounceContract.claim announce ↔ Sharing.announceContract.claim announce := by
  simp only [Old.AnnounceContract.claim, Sharing.announceContract.claim, Old.AnnounceContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem approveContract_eq (approve : Library → Int → PersonId → PersonId → Target → Library) (isPending : AccessRequest → Int → Prop) (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop) :
    Old.ApproveContract.claim isPending mayEdit ownedBy approve ↔ Sharing.approveContract.claim approve isPending mayEdit ownedBy := by
  simp only [Old.ApproveContract.claim, Sharing.approveContract.claim, Old.ApproveContract.post,
    PortEq.sharesWithout_eq, PortEq.requestsWithout_eq, Sharing.granted]
  constructor <;> intro h lib t b p w <;> rw [h] <;> split <;> rename_i r heq <;> simp only [heq]
  all_goals first
    | rfl
    | (have hr := List.find?_some heq
       simp only [decide_eq_true_eq] at hr
       obtain ⟨⟨hp, hw⟩, _⟩ := hr
       subst hp; subst hw; rfl)

theorem askContract_eq (ask : Library → Int → PersonId → Target → Level → Library) :
    Old.AskContract.claim ask ↔ Sharing.askContract.claim ask := by
  simp only [Old.AskContract.claim, Sharing.askContract.claim, Old.AskContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem chaseContract_eq (chase : Library → Int → Library) (isPending : AccessRequest → Int → Prop) (reminderDue : AccessRequest → Int → Prop) :
    Old.ChaseContract.claim isPending reminderDue chase ↔ Sharing.chaseContract.claim chase isPending reminderDue := by
  simp only [Old.ChaseContract.claim, Sharing.chaseContract.claim, Old.ChaseContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem clockNeverGoesBack_eq (events : (List Event)) :
    Old.ClockNeverGoesBack.claim events ↔ Sharing.clockNeverGoesBack.claim events := by
  simp only [Old.ClockNeverGoesBack.claim, Sharing.clockNeverGoesBack.claim]
  constructor
  · intro h pre e post hx; have := h pre post e hx; cases e <;> simp_all
  · intro h pre post e hx; have := h pre e post hx; cases e <;> simp_all

theorem declineContract_eq (decline : Library → Int → PersonId → PersonId → Target → Library) (mayEdit : Library → Int → PersonId → Target → Prop) :
    Old.DeclineContract.claim mayEdit decline ↔ Sharing.declineContract.claim decline mayEdit := by
  simp only [Old.DeclineContract.claim, Sharing.declineContract.claim, Old.DeclineContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem forgetContract_eq (forget : Library → Int → Library) :
    Old.ForgetContract.claim forget ↔ Sharing.forgetContract.claim forget := by
  simp only [Old.ForgetContract.claim, Sharing.forgetContract.claim, Old.ForgetContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem housekeepingClearsOnlyTheEnded_eq (tidy : Library → Int → Library) (inForce : Share → Int → Prop) (gone : Document → Int → Prop) (isOpen : Invitation → Int → Prop) :
    Old.HousekeepingClearsOnlyTheEnded.claim tidy inForce gone isOpen ↔ Sharing.housekeepingClearsOnlyTheEnded.claim tidy inForce gone isOpen := by
  simp only [Old.HousekeepingClearsOnlyTheEnded.claim, Sharing.housekeepingClearsOnlyTheEnded.claim, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem inviteContract_eq (invite : Library → Int → PersonId → PersonId → Target → Level → Library) (mayEdit : Library → Int → PersonId → Target → Prop) :
    Old.InviteContract.claim mayEdit invite ↔ Sharing.inviteContract.claim invite mayEdit := by
  simp only [Old.InviteContract.claim, Sharing.inviteContract.claim, Old.InviteContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem moveContract_eq (move : Library → Int → PersonId → DocumentId → (Option FolderId) → Library) (mayEdit : Library → Int → PersonId → Target → Prop) :
    Old.MoveContract.claim mayEdit move ↔ Sharing.moveContract.claim move mayEdit := by
  simp only [Old.MoveContract.claim, Sharing.moveContract.claim, Old.MoveContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem ownersKeepTheirDocuments_eq (transfer : Library → Int → PersonId → DocumentId → PersonId → Library) (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop) (unshare : Library → Int → PersonId → Target → Grantee → Library) (share : Library → Int → PersonId → Share → Library) :
    Old.OwnersKeepTheirDocuments.claim transfer mayEdit ownedBy unshare share ↔ Sharing.ownersKeepTheirDocuments.claim transfer mayEdit ownedBy unshare share := by
  simp only [Old.OwnersKeepTheirDocuments.claim, Sharing.ownersKeepTheirDocuments.claim, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem recordContract_eq (record : Library → Int → Change → Library) :
    Old.RecordContract.claim record ↔ Sharing.recordContract.claim record := by
  simp only [Old.RecordContract.claim, Sharing.recordContract.claim, Old.RecordContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem restoreContract_eq (restore : Library → Int → PersonId → DocumentId → Library) (gone : Document → Int → Prop) (mayEdit : Library → Int → PersonId → Target → Prop) :
    Old.RestoreContract.claim gone mayEdit restore ↔ Sharing.restoreContract.claim restore gone mayEdit := by
  simp only [Old.RestoreContract.claim, Sharing.restoreContract.claim, Old.RestoreContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem shareContract_eq (share : Library → Int → PersonId → Share → Library) (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop) :
    Old.ShareContract.claim mayEdit ownedBy share ↔ Sharing.shareContract.claim share mayEdit ownedBy := by
  simp only [Old.ShareContract.claim, Sharing.shareContract.claim, Old.ShareContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem tidyContract_eq (tidy : Library → Int → Library) (gone : Document → Int → Prop) (inForce : Share → Int → Prop) (isOpen : Invitation → Int → Prop) :
    Old.TidyContract.claim gone inForce isOpen tidy ↔ Sharing.tidyContract.claim tidy gone inForce isOpen := by
  simp only [Old.TidyContract.claim, Sharing.tidyContract.claim, Old.TidyContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem transferContract_eq (transfer : Library → Int → PersonId → DocumentId → PersonId → Library) (mayEdit : Library → Int → PersonId → Target → Prop) :
    Old.TransferContract.claim mayEdit transfer ↔ Sharing.transferContract.claim transfer mayEdit := by
  simp only [Old.TransferContract.claim, Sharing.transferContract.claim, Old.TransferContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem trashContract_eq (trash : Library → Int → PersonId → DocumentId → Library) (mayEdit : Library → Int → PersonId → Target → Prop) :
    Old.TrashContract.claim mayEdit trash ↔ Sharing.trashContract.claim trash mayEdit := by
  simp only [Old.TrashContract.claim, Sharing.trashContract.claim, Old.TrashContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem unshareContract_eq (unshare : Library → Int → PersonId → Target → Grantee → Library) (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop) :
    Old.UnshareContract.claim mayEdit ownedBy unshare ↔ Sharing.unshareContract.claim unshare mayEdit ownedBy := by
  simp only [Old.UnshareContract.claim, Sharing.unshareContract.claim, Old.UnshareContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem warnContract_eq (warn : Library → Int → Library) :
    Old.WarnContract.claim warn ↔ Sharing.warnContract.claim warn := by
  simp only [Old.WarnContract.claim, Sharing.warnContract.claim, Old.WarnContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))

theorem withdrawContract_eq (withdraw : Library → Int → PersonId → PersonId → Target → Library) (mayEdit : Library → Int → PersonId → Target → Prop) :
    Old.WithdrawContract.claim mayEdit withdraw ↔ Sharing.withdrawContract.claim withdraw mayEdit := by
  simp only [Old.WithdrawContract.claim, Sharing.withdrawContract.claim, Old.WithdrawContract.post, PortEq.askCode_eq, PortEq.chaseCode_eq, PortEq.chaseNotices_eq, PortEq.chased_eq, PortEq.declineCode_eq, PortEq.holds_eq, PortEq.isFor_eq, PortEq.requestsWithout_eq, PortEq.recordCode_eq, PortEq.ofGone_eq, PortEq.tidyCode_eq, PortEq.invitationsWithout_eq, PortEq.inviteCode_eq, PortEq.withdrawCode_eq, PortEq.isOpenCode_eq, PortEq.isPendingCode_eq, PortEq.reminderDueCode_eq, PortEq.announceCode_eq, PortEq.endingNotices_eq, PortEq.endsInADay_eq, PortEq.firstOfEach_eq, PortEq.mailbox_eq, PortEq.noticesOf_eq, PortEq.reachedBy_eq, PortEq.taken_eq, PortEq.warnCode_eq, PortEq.accessCode_eq, PortEq.canEditCode_eq, PortEq.canViewCode_eq, PortEq.granteesOf_eq, PortEq.placesOf_eq, PortEq.shareCode_eq, PortEq.sharesWithout_eq, PortEq.strongest_eq, PortEq.unshareCode_eq, PortEq.owns_eq, PortEq.transferCode_eq, PortEq.mayRestore_eq, PortEq.restoreCode_eq, PortEq.trashCode_eq, PortEq.inForceCode_eq, PortEq.goneCode_eq, PortEq.mayMove_eq, PortEq.foldersAt_eq, PortEq.acceptCode_eq, PortEq.moveCode_eq, PortEq.makes_eq, PortEq.explains_eq, PortEq.forgetCode_eq, PortEq.approveCode_eq, PortEq.answered_eq, PortEq.answerTo_eq]
  all_goals first
    | exact Iff.rfl
    | (constructor <;> intro h <;> intros <;> rw [h] <;> (first | rfl | (congr 1) | simp))


-- Today's words were defines, not nodes: each meets the claim the port states of its word.

theorem reach_today : Sharing.reach.claim Old.reaches := by
  unfold Sharing.reach.claim; intro lib s p; rfl

theorem cover_today : Sharing.cover.claim Old.covers := by
  unfold Sharing.cover.claim; intro lib s x; rfl

theorem permission_today (inForce : Share → Int → Prop) :
    Sharing.permission.claim (Old.mayView inForce Old.reaches Old.covers) inForce Old.reaches Old.covers := by
  unfold Sharing.permission.claim; intro lib t p x; rfl

theorem editPermission_today (inForce : Share → Int → Prop) :
    Sharing.editPermission.claim (Old.mayEdit inForce Old.reaches Old.covers) inForce Old.reaches Old.covers := by
  unfold Sharing.editPermission.claim; intro lib t p x; rfl

theorem whoMayEdit_today (inForce : Share → Int → Prop) :
    Sharing.whoMayEdit.claim (Old.mayEdit inForce Old.reaches Old.covers) inForce Old.reaches Old.covers := by
  unfold Sharing.whoMayEdit.claim; intro lib t p x; rfl

theorem inTrash_today : Sharing.inTrash.claim Old.inTrash := by
  unfold Sharing.inTrash.claim; intro lib d; rfl

theorem whatIsTrashed_today : Sharing.whatIsTrashed.claim Old.inTrash := by
  unfold Sharing.whatIsTrashed.claim; intro lib d; rfl

theorem ownersShare_today : Sharing.ownersShare.claim Old.ownedBy := by
  unfold Sharing.ownersShare.claim; intro lib what withWhom; rfl

theorem invitationLifetime_today : Sharing.invitationLifetime.claim Old.invitationLasts := rfl
theorem trashLifetime_today : Sharing.trashLifetime.claim Old.trashKeeps := rfl
theorem requestLifetime_today : Sharing.requestLifetime.claim Old.requestLasts := rfl
theorem reminderTime_today : Sharing.reminderTime.claim Old.remindAfter := rfl
theorem housekeepingPeriod_today : Sharing.housekeepingPeriod.claim Old.housekeepingWithin := rfl

end Port
