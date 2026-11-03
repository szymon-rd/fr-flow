import FrFlowGen.Sharing.logKept.Spec
import Proofs.Sharing.Lemmas

/-! The log's account kept at every step of the run (`logKept`): every share held has the entry that made it, every
notice of a change the entry it tells of. Each operation is its code, as its contract says. A request handled leaves
the library as it was or served at a moment (handleContract), a request served making only shares its entry tells of,
the entries before kept and its notices of its entry; a run of housekeeping leaves it housekept (housekeepingJob),
forgetting no entry that explains a share or a notice it keeps, its own notices of no logged change; delivery takes
notices out of the outbox and touches nothing else of the library (deliveryJob). A run that fails changes none of
it. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.logKept.Proofs
open Sharing

theorem cover_deliver : Obl.cover_deliver := by
  unfold Obl.cover_deliver Sharing.logKept.keeps_deliver
  intro before g1 g2 g3
  have h := Lemmas.delivery_job before g1 g2 g3
  revert h
  cases delivery_run before with
  | mk res after =>
    cases res with
    | error e =>
      intro h
      obtain ⟨hlib, _⟩ := h.2
      refine ⟨trivial, ?_⟩
      show logKept after.libraryModel
      rw [hlib]; exact g3
    | ok u =>
      intro h
      obtain ⟨⟨hlib, _⟩, _⟩ := h.1
      refine ⟨?_, trivial⟩
      show logKept after.libraryModel
      rw [hlib]
      refine ⟨g3.1, fun n hn => g3.2 n ?_⟩
      exact (List.mem_filter.1 hn).1

theorem cover_housekeep : Obl.cover_housekeep := by
  unfold Obl.cover_housekeep
  intro warn chase forget tidy record isPending reminderDue canView inTheTrash mayView canEdit allowedToEdit share
    unshare move withdraw invite accept isOpen trash restore ask approve decline transfer inForce gone handle announce
    access mayEdit ownedBy hWarn hJob hChase hForget _ _ hTidy hRecord _
  generalize housekeeping_run warn chase forget tidy record = housekeep at hJob ⊢
  have eW : warn = warnCode := by funext a b; rw [hWarn]; rfl
  have eC : chase = chaseCode isPending reminderDue := by funext a b; rw [hChase]; rfl
  have eF : forget = forgetCode := by funext a b; rw [hForget]; rfl
  have eT : tidy = tidyCode gone inForce isOpen := by funext a b; rw [hTidy]; rfl
  have eR : record = recordCode := by funext a b c; rw [hRecord]; rfl
  subst eW eC eF eT eR
  unfold Sharing.logKept.keeps_housekeep
  intro before g1 g2 g3
  have h := hJob before g1 g2 g3
  revert h
  cases housekeep before with
  | mk res after =>
    cases res with
    | error e =>
      intro h
      obtain ⟨_, _, hlib, _⟩ := h.2
      refine ⟨trivial, ?_⟩
      show logKept after.libraryModel
      rw [hlib]; exact g3
    | ok u =>
      intro h
      obtain ⟨⟨hlib, _⟩, _⟩ := h.1
      refine ⟨?_, trivial⟩
      show logKept after.libraryModel
      rw [hlib]
      exact Lemmas.housekept_logKept isPending reminderDue gone inForce isOpen before.libraryModel
        before.clockModel g3

theorem cover_handle : Obl.cover_handle := by
  unfold Obl.cover_handle
  intro announce record share unshare move invite accept withdraw trash restore ask approve decline transfer access
    mayEdit ownedBy isOpen isPending gone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hAnnounce hHandle hRecord _ _ _ hShare hUnshare hMove _ hInvite hAccept hWithdraw _ hTrash hRestore _ hAsk hApprove
    hDecline hTransfer
  intros
  generalize handleRequest_run announce record share unshare move invite accept withdraw trash restore ask approve
    decline transfer access mayEdit ownedBy isOpen isPending gone = handle at hHandle ⊢
  have eA : announce = announceCode := by funext a b c d; rw [hAnnounce]; rfl
  have eR : record = recordCode := by funext a b c; rw [hRecord]; rfl
  have e1 : share = shareCode mayEdit ownedBy := by funext a b c d; rw [hShare]; rfl
  have e2 : unshare = unshareCode mayEdit ownedBy := by funext a b c d e; rw [hUnshare]; rfl
  have e3 : move = moveCode mayEdit := by funext a b c d e; rw [hMove]; rfl
  have e4 : invite = inviteCode mayEdit := by funext a b c d e f; rw [hInvite]; rfl
  have e5 : accept = acceptCode isOpen ownedBy := by funext a b c d; rw [hAccept]; rfl
  have e6 : withdraw = withdrawCode mayEdit := by funext a b c d e; rw [hWithdraw]; rfl
  have e7 : trash = trashCode mayEdit := by funext a b c d; rw [hTrash]; rfl
  have e8 : restore = restoreCode gone mayEdit := by funext a b c d; rw [hRestore]; rfl
  have e9 : ask = askCode := by funext a b c d e; rw [hAsk]; rfl
  have e10 : approve = approveCode isPending mayEdit ownedBy := by funext a b c d e; rw [hApprove]; rfl
  have e11 : decline = declineCode mayEdit := by funext a b c d e; rw [hDecline]; rfl
  have e12 : transfer = transferCode mayEdit := by funext a b c d e; rw [hTransfer]; rfl
  subst eA eR e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  unfold Sharing.logKept.keeps_handle
  intro r before g1 g2 g3
  have h := hHandle r before g1 g2 g3
  revert h
  cases handle r before with
  | mk res after =>
    cases res with
    | error e =>
      intro h
      obtain ⟨_, _, hlib, _⟩ := h.2
      refine ⟨trivial, ?_⟩
      show logKept after.libraryModel
      rw [hlib]; exact g3
    | ok result =>
      intro h
      obtain ⟨⟨hex, _⟩, _⟩ := h.1
      obtain ⟨t, ⟨_, hlib⟩, _⟩ := not_forall_not.mp hex
      refine ⟨?_, trivial⟩
      show logKept after.libraryModel
      rw [hlib]
      exact Lemmas.served_logKept mayEdit ownedBy isOpen gone isPending before.libraryModel t r g3

end Sharing.logKept.Proofs
