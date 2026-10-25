import FrFlowGen.Sharing.Domain

/-! Facts shared by the authored proofs. What a change made by an `if` says of its condition. And, for the claims over
runs, what an event does to the library: a request answered at `t` stamps only `t` (an invitation it leaves is one the
library held or one sent at `t`; a document it leaves has no trash time, the time `t`, or the trash time of a document
the library held; a request it leaves is one the library held, or one made at `t`, not reminded); recording a change
touches only the log, announcing it only the outbox (RecordContract, AnnounceContract), chasing the requests only the
requests and the outbox. -/

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


/-- A request's library, as the operation left it (recorded and announced), or as it was. -/
theorem served_eq (announce : Library → Library → Request → Entry → Library) (record : Library → Int → Change → Library)
    (hR : ∀ l t c, record l t c = { l with log := l.log ++ [Entry.mk (l.log.length : Int) t c] }) (hA : ∀ l b r e, announce l b r e = { l with outbox := l.outbox ++ Notifications.noticesOf b r e }) mayEdit ownedBy isOpen gone isPending (lib : Library) (t : Int) (r : Request) :
    Run.served announce record mayEdit ownedBy isOpen gone isPending lib t r =
      if Run.answered mayEdit ownedBy isOpen gone isPending lib t r ≠ lib then
        { Run.answered mayEdit ownedBy isOpen gone isPending lib t r with
          log := (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).log ++
            [Entry.mk ((Run.answered mayEdit ownedBy isOpen gone isPending lib t r).log.length : Int) t (Change.Made r)],
          outbox := (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).outbox ++
            Notifications.noticesOf lib r (Entry.mk ((Run.answered mayEdit ownedBy isOpen gone isPending lib t r).log.length : Int) t (Change.Made r)) }
      else lib := by
  simp only [Run.served, hA, hR]

/-- A run of housekeeping's library: tidied, its requests chased, recorded; or as it was. -/
theorem housekept_eq (record : Library → Int → Change → Library) (hR : ∀ l t c, record l t c = { l with log := l.log ++ [Entry.mk (l.log.length : Int) t c] }) isPending reminderDue gone inForce isOpen
    (lib : Library) (t : Int) :
    Run.housekept record isPending reminderDue gone inForce isOpen lib t =
      if AccessRequests.chaseCode isPending reminderDue (Housekeeping.tidyCode gone inForce isOpen lib t) t ≠ lib then
        { AccessRequests.chaseCode isPending reminderDue (Housekeeping.tidyCode gone inForce isOpen lib t) t with
          log := (AccessRequests.chaseCode isPending reminderDue (Housekeeping.tidyCode gone inForce isOpen lib t) t).log ++
            [Entry.mk ((AccessRequests.chaseCode isPending reminderDue (Housekeeping.tidyCode gone inForce isOpen lib t) t).log.length : Int) t Change.Housekept] }
      else lib := by
  simp only [Run.housekept, hR]

theorem answered_invitations (mayEdit : Library → Int → PersonId → Target → Prop) ownedBy (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) isPending (lib : Library) (t : Int) (r : Request) :
    ∀ i ∈ (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).invitations, i ∈ lib.invitations ∨ i.sent = t := by
  intro i hi
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode, AccessRequests.askCode,
    AccessRequests.approveCode, AccessRequests.declineCode, Ownership.transferCode] at hi <;>
    (try split at hi) <;> (try split at hi) <;> simp_all [Invitations.invitationsWithout, List.mem_filter]
  all_goals rcases hi with rfl | ⟨h, _⟩ <;> simp_all

theorem answered_documents (mayEdit : Library → Int → PersonId → Target → Prop) ownedBy (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) isPending (lib : Library) (t : Int) (r : Request) :
    ∀ doc ∈ (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).documents,
      doc.trashed = none ∨ doc.trashed = some t ∨ ∃ x ∈ lib.documents, x.trashed = doc.trashed := by
  intro doc hd
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode, AccessRequests.askCode,
    AccessRequests.approveCode, AccessRequests.declineCode, Ownership.transferCode] at hd <;>
    (try split at hd) <;> (try split at hd) <;> (try simp only [List.mem_map] at hd)
  all_goals first
    | exact Or.inr (Or.inr ⟨doc, hd, rfl⟩)
    | (obtain ⟨x, hx, rfl⟩ := hd; split <;> first | exact Or.inr (Or.inr ⟨x, hx, rfl⟩) | simp_all)
    | simp_all

theorem answered_requests (mayEdit : Library → Int → PersonId → Target → Prop) ownedBy (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) isPending (lib : Library) (t : Int) (r : Request) :
    ∀ q ∈ (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).requests, q ∈ lib.requests ∨ (q.asked = t ∧ ¬ q.reminded) := by
  intro q hq
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode, AccessRequests.askCode,
    AccessRequests.approveCode, AccessRequests.declineCode, Ownership.transferCode] at hq <;>
    (try split at hq) <;> (try split at hq) <;> simp_all [AccessRequests.requestsWithout, List.mem_filter]
  all_goals rcases hq with rfl | ⟨h, _⟩ <;> simp_all

/-- The operations leave the log alone. -/
theorem answered_log (mayEdit : Library → Int → PersonId → Target → Prop) ownedBy (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) isPending (lib : Library) (t : Int) (r : Request) :
    (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).log = lib.log := by
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode, AccessRequests.askCode,
    AccessRequests.approveCode, AccessRequests.declineCode, Ownership.transferCode] <;>
    (try split) <;> (try split) <;> rfl

/-- A share a request leaves is one the library held, or one the request made (as its log entry says). -/
theorem answered_shares (mayEdit : Library → Int → PersonId → Target → Prop) ownedBy (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) isPending (lib : Library) (t : Int) (r : Request) (n : Int) :
    ∀ s ∈ (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).shares,
      s ∈ lib.shares ∨ Audit.makes (Entry.mk n t (Change.Made r)) s := by
  intro s hs
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode, AccessRequests.askCode,
    AccessRequests.approveCode, AccessRequests.declineCode, Ownership.transferCode] at hs <;>
    (try split at hs) <;> (try split at hs) <;>
    simp_all [Sharing.sharesWithout, List.mem_filter, Audit.makes]
  all_goals rcases hs with h | ⟨h, _⟩ <;> simp_all

/-- The operations leave the outbox alone. -/
theorem answered_outbox (mayEdit : Library → Int → PersonId → Target → Prop) ownedBy (isOpen : Invitation → Int → Prop)
    (gone : Document → Int → Prop) isPending (lib : Library) (t : Int) (r : Request) :
    (Run.answered mayEdit ownedBy isOpen gone isPending lib t r).outbox = lib.outbox := by
  cases r <;> simp only [Run.answered, Sharing.shareCode, Sharing.unshareCode, Sharing.moveCode, Invitations.inviteCode,
    Invitations.acceptCode, Invitations.withdrawCode, Trash.trashCode, Trash.restoreCode, AccessRequests.askCode,
    AccessRequests.approveCode, AccessRequests.declineCode, Ownership.transferCode] <;>
    (try split) <;> (try split) <;> rfl

/-- The notices of a change are all of its entry. -/
theorem noticesOf_logged (lib : Library) (r : Request) (e : Entry) : ∀ n ∈ Notifications.noticesOf lib r e, n.about = Subject.Logged e := by
  intro n hn
  cases r <;> simp only [Notifications.noticesOf, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hn <;>
    (try rcases hn with ⟨_, _, rfl⟩) <;> (try subst hn) <;> simp_all

/-- Housekeeping's notices are reminders and lapses, of no logged change. -/
theorem chaseNotices_unlogged isPending reminderDue (lib : Library) (t : Int) :
    ∀ n ∈ AccessRequests.chaseNotices isPending reminderDue lib t, ∀ e, n.about ≠ Subject.Logged e := by
  intro n hn e
  simp only [AccessRequests.chaseNotices, List.mem_append, List.mem_map, List.mem_flatMap] at hn
  rcases hn with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> simp

end Sharing.Lemmas
