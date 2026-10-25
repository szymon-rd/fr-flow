import FrFlowGen.Sharing.Domain

/-! Facts shared by the authored proofs. What a change made by an `if` says of its condition. And, for the deadlines,
what a request does to the times the library holds. A request
answered at `t` stamps only `t`: an invitation it leaves is one the library held or one sent at `t`; a document it
leaves has no trash time, the time `t`, or the trash time of a document the library held. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Lemmas
open Sharing

/-- A change made by an `if` whose other branch changes nothing: its condition held. -/
theorem changed {α : Type} {c : Prop} {inst : Decidable c} {a b : α} (h : @ite α c inst a b ≠ b) : c :=
  Classical.byContradiction fun hn => h (ite_eq_right hn)

/-- What reads a value the same on both branches of an `if` reads it the same on the `if`. -/
theorem ite_same {α β : Type} {c : Prop} {inst : Decidable c} (f : α → β) (a b : α) (h : f a = f b) :
    f (@ite α c inst a b) = f b := by
  split
  · exact h
  · rfl

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
