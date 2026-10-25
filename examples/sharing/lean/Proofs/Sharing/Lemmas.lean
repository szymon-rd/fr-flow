import FrFlowGen.Sharing.Domain

/-! Facts shared by the authored proofs of the deadlines: what a request does to the times the library holds. A request
answered at `t` stamps only `t`: an invitation it leaves is one the library held or one sent at `t`; a document it
leaves has no trash time, the time `t`, or the trash time of a document the library held. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Lemmas
open Sharing

theorem answered_invitations (mayEdit : Library → Int → PersonId → Target → Prop) (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) (lib : Library) (t : Int) (r : Request) :
    ∀ i ∈ (Run.answered mayEdit isOpen gone lib t r).invitations, i ∈ lib.invitations ∨ i.sent = t := by
  intro i hi
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode] at hi <;>
    (try split at hi) <;> simp_all [Invitations.invitationsWithout, List.mem_filter]
  all_goals rcases hi with rfl | ⟨h, _⟩ <;> simp_all

theorem answered_documents (mayEdit : Library → Int → PersonId → Target → Prop) (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) (lib : Library) (t : Int) (r : Request) :
    ∀ doc ∈ (Run.answered mayEdit isOpen gone lib t r).documents,
      doc.trashed = none ∨ doc.trashed = some t ∨ ∃ x ∈ lib.documents, x.trashed = doc.trashed := by
  intro doc hd
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode] at hd <;>
    (try split at hd) <;> (try simp only [List.mem_map] at hd)
  all_goals first
    | exact Or.inr (Or.inr ⟨doc, hd, rfl⟩)
    | (obtain ⟨x, hx, rfl⟩ := hd; split <;> first | exact Or.inr (Or.inr ⟨x, hx, rfl⟩) | simp_all)

end Sharing.Lemmas
