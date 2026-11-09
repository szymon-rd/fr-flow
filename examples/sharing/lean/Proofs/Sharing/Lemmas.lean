import FrFlowGen.Sharing.Domain
import FrFlowGen.Sharing.deliveryJob.Spec

/-! Facts the sharing proofs share: an `if` that changed a value took its branch; what each request leaves of the
documents, the invitations and the requests; and that recording and announcing it touch only the log and the
outbox. A request is served, and housekeeping run, by the operations' code (`afterRequest`, `served`, `housekeptAt`
with each operation its code, which each operation's contract says it is). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Lemmas

/-- An `if` whose value is not its `else` branch's took its `then` branch. -/
theorem changed {α : Type} {c : Prop} {inst : Decidable c} {a b : α} (h : ¬ (@ite α c inst a b = b)) : c :=
  Classical.byContradiction fun hn => h (ite_eq_right hn)

/-- Who a share must be with, as accessContract lists them, is whom it reaches. -/
theorem with_iff (lib : Library) (p : PersonId) (g : Grantee) :
    g ∈ granteesOf lib p ↔ (match g with
      | Grantee.Person q => q = p
      | Grantee.Team t => ∃ team ∈ lib.teams, team.id_ = t ∧ p ∈ team.members) := by
  cases g with
  | Person q => simp [granteesOf]
  | Team t =>
    simp only [granteesOf, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq, reduceCtorEq, false_or,
      Grantee.Team.injEq]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, h3⟩; exact ⟨a, h1, h3, h2⟩
    · rintro ⟨a, h1, h3, h2⟩; exact ⟨a, ⟨h1, h2⟩, h3⟩

/-- What a share must be of, as accessContract lists it, is what covers the document. -/
theorem of_iff (lib : Library) (d : DocumentId) (t : Target) :
    t ∈ placesOf lib d ↔ (match t with
      | Target.Doc e => Target.Doc d = Target.Doc e
      | Target.InFolder f => ∃ doc ∈ lib.documents, doc.id_ = d ∧ f ∈ doc.folders) := by
  cases t with
  | Doc e => simp [placesOf, eq_comm]
  | InFolder f =>
    simp only [placesOf, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
      reduceCtorEq, false_or, Target.InFolder.injEq]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, b, h3, rfl⟩; exact ⟨a, h1, h2, h3⟩
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, ⟨h1, h2⟩, f, h3, rfl⟩

/-- A request served: as it was, or what its operation left, recorded and announced, which changes the documents,
the invitations, the requests and the shares no more. -/
theorem served_cases (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) = lib ∨
      (((served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).documents =
          ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).documents ∧
        ((served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).invitations =
          ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).invitations ∧
        ((served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).requests =
          ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).requests ∧
        ((served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).shares =
          ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).shares) := by
  simp only [served]
  split
  · exact Or.inr ⟨by simp [announceCode, recordCode], by simp [announceCode, recordCode],
      by simp [announceCode, recordCode], by simp [announceCode, recordCode]⟩
  · exact Or.inl rfl

/-- A document a request leaves is out of the trash, put there now, or in it since a time the library held. -/
theorem answered_documents (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    ∀ doc ∈ ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).documents,
      doc.trashed = none ∨ doc.trashed = some t ∨ ∃ x ∈ lib.documents, x.trashed = doc.trashed := by
  intro doc hd
  cases r <;> simp only [afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted, handedOn] at hd <;>
    (try split at hd) <;> (try split at hd) <;> (try simp only [List.mem_map] at hd)
  all_goals first
    | exact Or.inr (Or.inr ⟨doc, hd, rfl⟩)
    | (obtain ⟨x, hx, rfl⟩ := hd; split <;> first | exact Or.inr (Or.inr ⟨x, hx, rfl⟩) | simp_all)
    | simp_all

/-- An invitation a request leaves is one the library held, or one sent now. -/
theorem answered_invitations (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    ∀ i ∈ ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).invitations, i ∈ lib.invitations ∨ i.sent = t := by
  intro i hi
  cases r <;> simp only [afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hi <;>
    (try split at hi) <;> (try split at hi) <;> simp_all [invitationsWithout, List.mem_filter]
  all_goals rcases hi with rfl | ⟨h, _⟩ <;> simp_all

/-- A request for access a request leaves is one the library held, or one made now and not reminded. -/
theorem answered_requests (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    ∀ q ∈ ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).requests,
      q ∈ lib.requests ∨ (q.asked = t ∧ ¬ q.reminded) := by
  intro q hq
  cases r <;> simp only [afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hq <;>
    (try split at hq) <;> (try split at hq) <;> simp_all [requestsWithout, List.mem_filter]
  all_goals rcases hq with rfl | ⟨h, _⟩ <;> simp_all

/-- A request that changes the library is recorded at the end of the log, and announced in the outbox, in the same
step; one that does not leaves the library as it was. -/
theorem served_logged (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) = lib ∨
      (((served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).shares =
          ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).shares ∧
        ((served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).log =
          ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).log ++
            [Entry.mk (((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).log.length : Int) t (Change.Made r)] ∧
        ((served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).outbox =
          ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).outbox ++
            noticesOf lib r (Entry.mk (((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).log.length : Int) t
              (Change.Made r))) := by
  simp only [served]
  split
  · exact Or.inr ⟨by simp [announceCode, recordCode], by simp [announceCode, recordCode],
      by simp [announceCode, recordCode]⟩
  · exact Or.inl rfl

/-- The operations leave the log alone. -/
theorem answered_log (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).log = lib.log := by
  cases r <;> simp only [afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] <;> (try split) <;> (try split) <;> rfl

/-- The operations leave the outbox alone. -/
theorem answered_outbox (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).outbox = lib.outbox := by
  cases r <;> simp only [afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] <;> (try split) <;> (try split) <;> rfl

/-- A share a request leaves is one the library held, or one the request made (as its log entry says). -/
theorem answered_shares (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) (n : Int) :
    ∀ s ∈ ((afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r)).shares,
      s ∈ lib.shares ∨ makes (Entry.mk n t (Change.Made r)) s := by
  intro s hs
  cases r <;> simp only [afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hs <;>
    (try split at hs) <;> (try split at hs) <;>
    simp_all [sharesWithout, List.mem_filter, makes, madeBy, ownersEdit]
  all_goals rcases hs with h | ⟨h, _⟩ <;> simp_all
  all_goals rename_i hq _
  all_goals have := List.find?_some hq
  all_goals simp_all

/-- What a run of housekeeping leaves of the documents, the invitations and the requests is what tidying and chasing
leave of them: forgetting old entries, telling of ending shares and recording the run touch none of them. -/
theorem housekept_parts (isPending reminderDue : AccessRequest → Int → Prop) (gone : Document → Int → Prop)
    (inForce : Share → Int → Prop) (isOpen : Invitation → Int → Prop) (lib : Library) (t : Int) :
    ((housekeptAt warnCode (chaseCode isPending reminderDue) forgetCode (tidyCode gone inForce isOpen) recordCode lib t)).documents = (tidyCode gone inForce isOpen lib t).documents ∧
      ((housekeptAt warnCode (chaseCode isPending reminderDue) forgetCode (tidyCode gone inForce isOpen) recordCode lib t)).invitations =
        (tidyCode gone inForce isOpen lib t).invitations ∧
      ((housekeptAt warnCode (chaseCode isPending reminderDue) forgetCode (tidyCode gone inForce isOpen) recordCode lib t)).requests =
        (chaseCode isPending reminderDue (tidyCode gone inForce isOpen lib t) t).requests := by
  simp only [housekeptAt]
  split
  · simp [recordCode, warnCode, forgetCode, chaseCode]
  · next hn =>
    have h := Classical.not_not.mp hn
    exact ⟨(congrArg Library.documents h).symm, (congrArg Library.invitations h).symm,
      (congrArg Library.requests h).symm⟩

/-- A request's notices are of its entry. -/
theorem noticesOf_logged (lib : Library) (r : Request) (e : Entry) :
    ∀ n ∈ noticesOf lib r e, n.about = Subject.Logged e := by
  intro n hn
  cases r <;> simp only [noticesOf, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hn <;>
    (try rcases hn with ⟨_, _, rfl⟩) <;> (try subst hn) <;> simp_all

/-- Housekeeping's notices are reminders and lapses, of no logged change. -/
theorem chaseNotices_unlogged (isPending reminderDue : AccessRequest → Int → Prop) (lib : Library) (t : Int) :
    ∀ n ∈ chaseNotices isPending reminderDue lib t, ∀ e, n.about ≠ Subject.Logged e := by
  intro n hn e
  simp only [chaseNotices, List.mem_append, List.mem_map, List.mem_flatMap] at hn
  rcases hn with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> simp

/-- The notices of shares ending are of no logged change. -/
theorem endingNotices_unlogged (lib : Library) (t : Int) :
    ∀ n ∈ endingNotices lib t, ∀ e, n.about ≠ Subject.Logged e := by
  intro n hn e
  simp only [endingNotices, List.mem_flatMap, List.mem_map] at hn
  obtain ⟨_, _, _, _, rfl⟩ := hn
  simp

/-- A traverse whose every step succeeds and keeps `Inv` of what it has done so far succeeds, keeping it of all. -/
theorem mapM_inv {ε α β σ : Type} (f : α → ExceptT ε (StateM σ) β) (Inv : List α → σ → Prop)
    (h : ∀ done x s, Inv done s →
      (∃ b, (FrFlow.runOnE (f x) s).1 = .ok b) ∧ Inv (done ++ [x]) (FrFlow.runOnE (f x) s).2) :
    ∀ (xs done : List α) (s : σ), Inv done s →
      ∃ bs, (FrFlow.runOnE (xs.mapM f) s).1 = .ok bs ∧ Inv (done ++ xs) (FrFlow.runOnE (xs.mapM f) s).2 := by
  intro xs
  induction xs with
  | nil => intro done s hs; exact ⟨[], rfl, by simpa [FrFlow.runOnE_pure] using hs⟩
  | cons x xs ih =>
    intro done s hs
    obtain ⟨⟨b, hb⟩, h1⟩ := h done x s hs
    obtain ⟨bs, hbs, h2⟩ := ih (done ++ [x]) _ h1
    rw [List.mapM_cons, FrFlow.runOnE_bind]
    generalize hx : FrFlow.runOnE (f x) s = rx at hb h1 h2 hbs
    rcases rx with ⟨_ | b', s1⟩
    · cases hb
    · simp only at h1 h2 hbs ⊢
      rw [FrFlow.runOnE_bind]
      generalize hy : FrFlow.runOnE (List.mapM f xs) s1 = ry at hbs h2
      rcases ry with ⟨_ | bs', s2⟩
      · cases hbs
      · exact ⟨b' :: bs', rfl, by simpa [FrFlow.runOnE_pure] using h2⟩

/-- A traverse of `xs₀` whose every step succeeds and keeps `Inv` of what it has done so far, the step knowing where
it is in the list, succeeds, keeping it of all. -/
theorem mapM_along {ε α β σ : Type} (f : α → ExceptT ε (StateM σ) β) (Inv : List α → σ → Prop) (xs₀ : List α)
    (h : ∀ done x rest s, done ++ x :: rest = xs₀ → Inv done s →
      (∃ b, (FrFlow.runOnE (f x) s).1 = .ok b) ∧ Inv (done ++ [x]) (FrFlow.runOnE (f x) s).2) (s : σ)
    (h0 : Inv [] s) :
    ∃ bs, (FrFlow.runOnE (xs₀.mapM f) s).1 = .ok bs ∧ Inv xs₀ (FrFlow.runOnE (xs₀.mapM f) s).2 := by
  suffices key : ∀ (xs done : List α) (s : σ), done ++ xs = xs₀ → Inv done s →
      ∃ bs, (FrFlow.runOnE (xs.mapM f) s).1 = .ok bs ∧ Inv (done ++ xs) (FrFlow.runOnE (xs.mapM f) s).2 by
    simpa using key xs₀ [] s rfl h0
  intro xs
  induction xs with
  | nil => intro done s _ hs; exact ⟨[], rfl, by simpa [FrFlow.runOnE_pure] using hs⟩
  | cons x xs ih =>
    intro done s hsplit hs
    obtain ⟨⟨b, hb⟩, h1⟩ := h done x xs s hsplit hs
    obtain ⟨bs, hbs, h2⟩ := ih (done ++ [x]) _ (by simpa using hsplit) h1
    rw [List.mapM_cons, FrFlow.runOnE_bind]
    generalize hx : FrFlow.runOnE (f x) s = rx at hb h1 h2 hbs
    rcases rx with ⟨_ | b', s1⟩
    · cases hb
    · simp only at h1 h2 hbs ⊢
      rw [FrFlow.runOnE_bind]
      generalize hy : FrFlow.runOnE (List.mapM f xs) s1 = ry at hbs h2
      rcases ry with ⟨_ | bs', s2⟩
      · cases hbs
      · exact ⟨b' :: bs', rfl, by simpa [FrFlow.runOnE_pure] using h2⟩

/-- A person's mailbox once a notice is given to the mail server: theirs, the notice taken; anyone else's as it was. -/
theorem mailbox_with (boxes : PersonId → Option (List Notice)) (q p : PersonId) (ns : List Notice) :
    mailbox (withMailbox boxes q ns) p = if p = q then ns else mailbox boxes p := by
  by_cases h : p = q <;> simp [mailbox, withMailbox, h]

/-- Taking a notice twice is taking it once. -/
theorem taken_taken (ns : List Notice) (n : Notice) : taken (taken ns n) n = taken ns n := by
  unfold taken
  by_cases h : n ∈ ns <;> simp [h]

/-- Two first notices of one person in an outbox are one notice. -/
theorem firstOfEach_one (o : List Notice) (a b : Notice) (ha : a ∈ firstOfEach o) (hb : b ∈ firstOfEach o)
    (h : a.to = b.to) : a = b := by
  simp only [firstOfEach, List.mem_filter, decide_eq_true_eq] at ha hb
  have ha2 := ha.2
  rw [h] at ha2
  exact Option.some.inj (ha2.symm.trans hb.2)

/-- A list filtered by membership in itself is itself, however membership is decided. -/
theorem filter_mem_self {α : Type} (l : List α) {d : ∀ n, Decidable (n ∈ l)} :
    l.filter (fun n => @decide (n ∈ l) (d n)) = l :=
  List.filter_eq_self.2 (fun a ha => @decide_eq_true _ (d a) ha)

/-- A list filtered by membership in one of its filters is that filter, however membership is decided. -/
theorem filter_mem_filter {α : Type} (l : List α) (keep : α → Bool) {d : ∀ n, Decidable (n ∈ l.filter keep)} :
    l.filter (fun n => @decide (n ∈ l.filter keep) (d n)) = l.filter keep :=
  List.filter_congr (fun a ha => by
    by_cases hk : keep a = true
    · simp [hk, List.mem_filter.2 ⟨ha, hk⟩]
    · have : a ∉ l.filter keep := fun h => hk (List.mem_filter.1 h).2
      simp [hk, this])

/-- A notice taken is in the mailbox. -/
theorem mem_taken (ns : List Notice) (n : Notice) : n ∈ taken ns n := by
  unfold taken
  by_cases h : n ∈ ns <;> simp [h]

/-- A library rebuilt from its fields is itself. -/
theorem library_eta (l : Library) :
    Library.mk l.documents l.folders l.teams l.shares l.invitations l.requests l.log l.outbox = l := rfl

/-- Two of an outbox's first notices, taken as two elements of it (equal, or apart), are one notice or of two
people. -/
theorem firstOfEach_apart (o : List Notice) (a b : Notice)
    (h : List.Sublist [a, b] (firstOfEach o) ∨ List.Sublist [b, a] (firstOfEach o)) : a.to = b.to → a = b := by
  have ha : a ∈ firstOfEach o := h.elim (fun s => s.subset (by simp)) (fun s => s.subset (by simp))
  have hb : b ∈ firstOfEach o := h.elim (fun s => s.subset (by simp)) (fun s => s.subset (by simp))
  exact firstOfEach_one o a b ha hb

/-- Two sends at once, each with its own faults, in either order: the same outcomes (each its faults' alone), and
the same mailboxes: of two people, each one's by its own send; of one, the same notice, taken once. -/
theorem sends_commute (n₁ n₂ : Notice) (hto : n₁.to = n₂.to → n₁ = n₂) (w : World)
    (f₁ r₁ f₂ r₂ : List Bool) (t₁ t₂ : List Nat) :
    FrFlow.sameModels (fun w => { w with faults := [], races := [], ticks := [] }) (FrFlow.runOn ((do
        modify (fun w => { w with faults := f₁, races := r₁, ticks := t₁ })
        let one ← FrFlow.caught ((do
            let r_1 := n₁
            MailerModel.Ops.send r_1) : ExceptT Failure (StateM World) Unit)
        modify (fun w => { w with faults := f₂, races := r₂, ticks := t₂ })
        let two ← FrFlow.caught ((do
            let r_1 := n₂
            MailerModel.Ops.send r_1) : ExceptT Failure (StateM World) Unit)
        pure (one, two)) : StateM World ((Except Failure Unit) × (Except Failure Unit))) w) (FrFlow.runOn ((do
        modify (fun w => { w with faults := f₂, races := r₂, ticks := t₂ })
        let two ← FrFlow.caught ((do
            let r_1 := n₂
            MailerModel.Ops.send r_1) : ExceptT Failure (StateM World) Unit)
        modify (fun w => { w with faults := f₁, races := r₁, ticks := t₁ })
        let one ← FrFlow.caught ((do
            let r_1 := n₁
            MailerModel.Ops.send r_1) : ExceptT Failure (StateM World) Unit)
        pure (one, two)) : StateM World ((Except Failure Unit) × (Except Failure Unit))) w) := by
  rcases w with ⟨mail, hk, c, lib, pool, fs, rs, ts⟩
  rcases f₁ with _ | ⟨_ | _, f₁⟩ <;> rcases f₂ with _ | ⟨_ | _, f₂⟩ <;>
    simp only [FrFlow.runOn_bind, FrFlow.runOn_modify, FrFlow.runOn_pure, FrFlow.runOn_caught, FrFlow.runOnE_failing,
      MailerModel.Ops.send_onWorldE, FrFlow.runOn_within, MailerModel.send, FrFlow.runOn_get, FrFlow.runOn_set,
      FrFlow.runOn_bind, FrFlow.sameModels, World.mk.injEq, and_true, true_and] <;>
    first
      | rfl
      | (by_cases h : n₁.to = n₂.to
         · obtain rfl := hto h
           simp [Lemmas.mailbox_with, Lemmas.taken_taken]
         · funext k
           simp only [withMailbox, mailbox]
           by_cases k₁ : k = n₁.to <;> by_cases k₂ : k = n₂.to <;> simp_all)

/-- Two removals of notices from the outbox at once, each a transaction with its own faults, in either order: the
same outcomes (each its faults' alone), and the same outbox, two filters in either order. -/
theorem removals_commute (n₁ n₂ : Notice) (w : World) (f₁ r₁ f₂ r₂ : List Bool) (t₁ t₂ : List Nat) :
    FrFlow.sameModels (fun w => { w with faults := [], races := [], ticks := [] }) (FrFlow.runOn ((do
        modify (fun w => { w with faults := f₁, races := r₁, ticks := t₁ })
        let one ← FrFlow.caught ((do
            let r_1 := n₁
            let r_2 ← LibraryModel.Ops.load
            LibraryModel.Ops.save { r_2 with outbox := (List.filter (fun m => decide (¬(m = r_1))) r_2.outbox) }
            pure ()) : ExceptT Failure (StateM World) Unit)
        modify (fun w => { w with faults := f₂, races := r₂, ticks := t₂ })
        let two ← FrFlow.caught ((do
            let r_1 := n₂
            let r_2 ← LibraryModel.Ops.load
            LibraryModel.Ops.save { r_2 with outbox := (List.filter (fun m => decide (¬(m = r_1))) r_2.outbox) }
            pure ()) : ExceptT Failure (StateM World) Unit)
        pure (one, two)) : StateM World ((Except Failure Unit) × (Except Failure Unit))) w) (FrFlow.runOn ((do
        modify (fun w => { w with faults := f₂, races := r₂, ticks := t₂ })
        let two ← FrFlow.caught ((do
            let r_1 := n₂
            let r_2 ← LibraryModel.Ops.load
            LibraryModel.Ops.save { r_2 with outbox := (List.filter (fun m => decide (¬(m = r_1))) r_2.outbox) }
            pure ()) : ExceptT Failure (StateM World) Unit)
        modify (fun w => { w with faults := f₁, races := r₁, ticks := t₁ })
        let one ← FrFlow.caught ((do
            let r_1 := n₁
            let r_2 ← LibraryModel.Ops.load
            LibraryModel.Ops.save { r_2 with outbox := (List.filter (fun m => decide (¬(m = r_1))) r_2.outbox) }
            pure ()) : ExceptT Failure (StateM World) Unit)
        pure (one, two)) : StateM World ((Except Failure Unit) × (Except Failure Unit))) w) := by
  rcases w with ⟨mail, hk, c, lib, pool, fs, rs, ts⟩
  rcases f₁ with _ | ⟨_ | _, _ | ⟨_ | _, f₁⟩⟩ <;> rcases f₂ with _ | ⟨_ | _, _ | ⟨_ | _, f₂⟩⟩ <;>
    simp only [FrFlow.runOn_bind, FrFlow.runOn_modify, FrFlow.runOn_pure, FrFlow.runOn_caught, FrFlow.runOnE_failing,
      FrFlow.runOnE_bind, FrFlow.runOnE_pure, LibraryModel.Ops.load_onWorldE, LibraryModel.Ops.save_onWorldE,
      FrFlow.runOn_within, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set,
      FrFlow.sameModels, World.mk.injEq, and_true, true_and, List.filter_filter] <;>
    first
      | rfl
      | (congr 2; funext m; exact Bool.and_comm _ _)

/-- A request served keeps the log's account (`sharesLogged`, `noticesLogged`): a share it makes comes with its entry,
the entries before stay (the operations leave the log alone), and its notices are of its entry. -/
theorem served_logKept (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) (h : sharesLogged lib ∧ noticesLogged lib) :
    sharesLogged (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) ∧ noticesLogged (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) := by
  simp only [sharesLogged, noticesLogged, logged, noticeLogged] at h ⊢
  rcases served_logged mayEdit ownedBy isOpen gone isPending lib t r with hc | ⟨hsh, hlog, hout⟩
  · rw [hc]; exact h
  · rw [answered_log] at hlog hout
    rw [answered_outbox] at hout
    refine ⟨fun s hs => ?_, fun n hn => ?_⟩
    · rw [hsh] at hs
      rw [hlog]
      rcases answered_shares mayEdit ownedBy isOpen gone isPending lib t r (lib.log.length : Int) s hs with h1 | h1
      · obtain ⟨e, he, hm⟩ := h.1 s h1
        exact ⟨e, List.mem_append_left _ he, hm⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), h1⟩
    · rw [hout] at hn
      rw [hlog]
      rcases List.mem_append.1 hn with hn | hn
      · have := h.2 n hn
        revert this
        cases n.about with
        | Logged e => exact fun he => List.mem_append_left _ he
        | _ => exact fun _ => trivial
      · rw [noticesOf_logged lib r _ n hn]
        exact List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- A run of housekeeping keeps the log's account: the shares it keeps are some of those held, each with its entry,
which forgetting keeps (it explains a share held); the notices before stay, each with its entry, which forgetting keeps
too (it explains a notice); its own notices are of no logged change; and its record goes at the end. -/
theorem housekept_logKept (isPending reminderDue : AccessRequest → Int → Prop) (gone : Document → Int → Prop)
    (inForce : Share → Int → Prop) (isOpen : Invitation → Int → Prop) (lib : Library) (t : Int)
    (h : sharesLogged lib ∧ noticesLogged lib) :
    sharesLogged (housekeptAt warnCode (chaseCode isPending reminderDue) forgetCode (tidyCode gone inForce isOpen) recordCode lib t) ∧
      noticesLogged (housekeptAt warnCode (chaseCode isPending reminderDue) forgetCode (tidyCode gone inForce isOpen) recordCode lib t) := by
  simp only [sharesLogged, noticesLogged, logged, noticeLogged] at h ⊢
  simp only [housekeptAt]
  split
  · refine ⟨fun s hs => ?_, fun n hn => ?_⟩
    · simp only [recordCode, warnCode, forgetCode, chaseCode, tidyCode, List.mem_filter, List.mem_append,
        List.mem_singleton] at hs ⊢
      obtain ⟨e, he, hm⟩ := h.1 s hs.1
      refine ⟨e, Or.inl (List.mem_map.2 ⟨e, he, ?_⟩), hm⟩
      exact if_neg (fun hx => hx.2 (Or.inl ⟨s, List.mem_filter.2 hs, hm⟩))
    · simp only [recordCode, warnCode, forgetCode, chaseCode, tidyCode, List.mem_append] at hn ⊢
      rcases hn with (hn | hn) | hn
      · have := h.2 n hn
        revert this
        cases hab : n.about with
        | Logged e =>
          intro he
          dsimp only
          refine Or.inl (List.mem_map.2 ⟨e, he, ?_⟩)
          exact if_neg (fun hx => hx.2 (Or.inr ⟨n, hn, hab⟩))
        | _ => exact fun _ => trivial
      · cases hab : n.about with
        | Logged e => exact absurd hab (chaseNotices_unlogged _ _ _ _ n hn e)
        | _ => trivial
      · cases hab : n.about with
        | Logged e => exact absurd hab (endingNotices_unlogged _ _ n hn e)
        | _ => trivial
  · exact h

/-- A world meeting every rule of the World: nothing held, housekeeping just run. What a branch says of every such
world and of no part of it holds through this one. -/
theorem quiet_world : ∃ w : World, housekeptLately w.clockModel w.housekeptModel ∧
    trashNotGoneAtHousekeeping w.libraryModel w.housekeptModel ∧
    invitationsOpenAtHousekeeping w.libraryModel w.housekeptModel ∧
    requestsPendingAtHousekeeping w.libraryModel w.housekeptModel ∧
    remindedAtHousekeeping w.libraryModel w.housekeptModel ∧ sharesLogged w.libraryModel ∧
    noticesLogged w.libraryModel :=
  ⟨⟨fun _ => none, 0, 0, Library.mk [] [] [] [] [] [] [] [], 0, [], [], []⟩, by simp [housekeptLately],
    by simp [trashNotGoneAtHousekeeping], by simp [invitationsOpenAtHousekeeping],
    by simp [requestsPendingAtHousekeeping], by simp [remindedAtHousekeeping], by simp [sharesLogged],
    by simp [noticesLogged]⟩

/-- The world's tick never takes the time back. -/
theorem tick_le (w : World) : w.clockModel ≤ (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) w).clockModel := by
  unfold FrFlow.Clock.ticked
  split
  · exact FrFlow.Clock.move_le (fun w : World => w.clockModel) _ _ _ _ (fun _ _ => rfl) (by simp; omega)
  · exact Int.le_refl _

/-- A look at the clock in a run that may fail: the time now, then the world's tick. -/
theorem now_run (s : World) :
    FrFlow.runOnE (ClockModel.Ops.now : ExceptT Failure (StateM World) Int) s = (.ok s.clockModel, (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) s)) := rfl

/-- A request served no earlier than housekeeping's last run leaves nothing that had ended by then: what it trashes,
sends or asks, it does now; the rest the library held. -/
theorem served_nothingEnded (mayEdit : Library → Int → PersonId → Target → Prop)
    (ownedBy : Library → Target → Grantee → Prop) (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop)
    (isPending : AccessRequest → Int → Prop) (lib : Library) (t : Int) (r : Request) (ran : Int)
    (h1 : trashNotGoneAtHousekeeping lib ran) (h2 : invitationsOpenAtHousekeeping lib ran)
    (h3 : requestsPendingAtHousekeeping lib ran) (h4 : remindedAtHousekeeping lib ran) (ht : ran ≤ t) :
    trashNotGoneAtHousekeeping (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) ran ∧
      invitationsOpenAtHousekeeping (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) ran ∧
      requestsPendingAtHousekeeping (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) ran ∧
      remindedAtHousekeeping (served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r) ran := by
  rcases served_cases mayEdit ownedBy isOpen gone isPending lib t r with hc | ⟨hd, hi, hq, _⟩
  · rw [hc]; exact ⟨h1, h2, h3, h4⟩
  · refine ⟨fun doc hdoc a ha => ?_, fun i hin => ?_, fun q hq' => ?_, fun q hq' => ?_⟩
    · rw [hd] at hdoc
      rcases answered_documents mayEdit ownedBy isOpen gone isPending lib t r doc hdoc with e | e | ⟨x, hx, e⟩
      · rw [e] at ha; cases ha
      · rw [e] at ha; cases ha; omega
      · exact h1 x hx a (e.trans ha)
    · rw [hi] at hin
      rcases answered_invitations mayEdit ownedBy isOpen gone isPending lib t r i hin with e | e
      · exact h2 i e
      · omega
    · rw [hq] at hq'
      rcases answered_requests mayEdit ownedBy isOpen gone isPending lib t r q hq' with e | ⟨e, _⟩
      · exact h3 q e
      · omega
    · rw [hq] at hq'
      rcases answered_requests mayEdit ownedBy isOpen gone isPending lib t r q hq' with e | ⟨e, _⟩
      · exact h4 q e
      · exact Or.inr (by omega)

/-- A notice's delivery keeps what a run of delivery keeps once it has sent `done` (from the library `lib` and
the mailboxes `boxes` it began with: the library is it, some of its outbox kept; each notice of the outbox is still
there, or was sent and the mail server has it; no one's mailbox not sent to has changed, and each one's sent to is as
it was or holds their notice): it leaves the library as it was or its outbox without the notice, the mail server
having it, and the mailboxes as they were or the notice's person's with it taken. -/
theorem delivery_kept (lib : Library) (boxes : PersonId → Option (List Notice)) (done rest : List Notice) (x : Notice) (s s' : World)
    (hsplit : done ++ x :: rest = firstOfEach lib.outbox) (hD : ((∃ keep : Notice → Bool, s.libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
      (∀ n ∈ lib.outbox, n ∈ s.libraryModel.outbox ∨ (n ∈ done ∧ n ∈ mailbox s.mailerModel n.to)) ∧
      (∀ p, (∀ n ∈ done, n.to ≠ p) → mailbox s.mailerModel p = mailbox boxes p) ∧
      (∀ n ∈ done, mailbox s.mailerModel n.to = mailbox boxes n.to ∨
        mailbox s.mailerModel n.to = taken (mailbox boxes n.to) n)))
    (eff : (s'.libraryModel = s.libraryModel ∧ (s'.mailerModel = s.mailerModel ∨ s'.mailerModel = withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x))) ∨
      (s'.libraryModel = { s.libraryModel with outbox := s.libraryModel.outbox.filter (fun m => decide ¬ m = x) } ∧
        s'.mailerModel = withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x))) :
    ((∃ keep : Notice → Bool, s'.libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
      (∀ n ∈ lib.outbox, n ∈ s'.libraryModel.outbox ∨ (n ∈ (done ++ [x]) ∧ n ∈ mailbox s'.mailerModel n.to)) ∧
      (∀ p, (∀ n ∈ (done ++ [x]), n.to ≠ p) → mailbox s'.mailerModel p = mailbox boxes p) ∧
      (∀ n ∈ (done ++ [x]), mailbox s'.mailerModel n.to = mailbox boxes n.to ∨
        mailbox s'.mailerModel n.to = taken (mailbox boxes n.to) n)) := by
  obtain ⟨⟨keep, hk⟩, h2, h3, h4⟩ := hD
  have hx : x ∈ firstOfEach lib.outbox := hsplit ▸ List.mem_append_right _ List.mem_cons_self
  have same : ∀ n ∈ done, n.to = x.to → n = x := fun n hn h =>
    Lemmas.firstOfEach_one _ _ _ (hsplit ▸ List.mem_append_left _ hn) hx h
  have hxbox : mailbox s.mailerModel x.to = mailbox boxes x.to ∨
      mailbox s.mailerModel x.to = taken (mailbox boxes x.to) x := by
    by_cases hin : ∃ n ∈ done, n.to = x.to
    · obtain ⟨n, hn, he⟩ := hin
      have := same n hn he
      subst this
      exact h4 n hn
    · exact Or.inl (h3 x.to (fun n hn he => hin ⟨n, hn, he⟩))
  have hW : ∀ p, mailbox (withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x)) p = if p = x.to then taken (mailbox s.mailerModel x.to) x
      else mailbox s.mailerModel p := fun p => Lemmas.mailbox_with _ _ _ _
  -- what a mailbox becomes: each person's as it was, but the notice's person's, its notice taken
  have boxOf : ∀ p, mailbox s'.mailerModel p = mailbox s.mailerModel p ∨
      (p = x.to ∧ mailbox s'.mailerModel p = taken (mailbox s.mailerModel x.to) x) := by
    intro p
    have hm : s'.mailerModel = s.mailerModel ∨ s'.mailerModel = withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x) := by
      rcases eff with ⟨_, hm⟩ | ⟨_, hm⟩
      · exact hm
      · exact Or.inr hm
    rcases hm with hm | hm
    · exact Or.inl (by rw [hm])
    · rw [hm, hW]
      by_cases hp : p = x.to
      · exact Or.inr ⟨hp, by simp [hp]⟩
      · exact Or.inl (by simp [hp])
  refine ⟨?_, fun n hn => ?_, fun p hp => ?_, fun n hn => ?_⟩
  · rcases eff with ⟨hl, _⟩ | ⟨hl, _⟩
    · exact ⟨keep, hl.trans hk⟩
    · refine ⟨fun m => keep m && decide ¬ m = x, ?_⟩
      rw [hl, hk]
      simp [List.filter_filter, Bool.and_comm]
  · rcases h2 n hn with hin | ⟨hd, hm⟩
    · rcases eff with ⟨hl, hm⟩ | ⟨hl, hm⟩
      · exact Or.inl (hl ▸ hin)
      · by_cases hnx : n = x
        · subst hnx
          refine Or.inr ⟨List.mem_append_right _ (List.mem_singleton.2 rfl), ?_⟩
          rw [hm, hW]
          simp [Lemmas.mem_taken]
        · exact Or.inl (by rw [hl]; simp [hin, hnx])
    · refine Or.inr ⟨List.mem_append_left _ hd, ?_⟩
      rcases boxOf n.to with hb | ⟨he, hb⟩
      · exact hb ▸ hm
      · have := same n hd he
        subst this
        rw [hb]
        exact Lemmas.mem_taken _ _
  · have hpx : x.to ≠ p := hp x (List.mem_append_right _ (List.mem_singleton.2 rfl))
    rcases boxOf p with hb | ⟨he, _⟩
    · exact hb.trans (h3 p (fun n hn => hp n (List.mem_append_left _ hn)))
    · exact absurd he.symm hpx
  · by_cases he : n.to = x.to
    · have hnx : n = x := by
        rcases List.mem_append.1 hn with hn | hn
        · exact same n hn he
        · simpa using hn
      subst hnx
      rcases boxOf n.to with hb | ⟨_, hb⟩
      · exact hb ▸ hxbox
      · rw [hb]
        rcases hxbox with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inr (by rw [h, Lemmas.taken_taken])
    · have hd : n ∈ done := by
        rcases List.mem_append.1 hn with hn | hn
        · exact hn
        · exact absurd (by simp at hn; rw [hn]) he
      rcases boxOf n.to with hb | ⟨he', _⟩
      · exact hb ▸ h4 n hd
      · exact absurd he' he

set_option maxHeartbeats 4000000 in
/-- A run of delivery does what deliveryJob says, for the proof of deliveryJob and of what delivery keeps. -/
theorem delivery_job : Sharing.deliveryJob.claim delivery_run := by
  unfold Sharing.deliveryJob.claim
  intro w _ _ _ _ _ _ _
  simp only [onlyTakenOut, sentFrom, tookAtMost]
  rcases w with ⟨boxes, hk, clock, lib, pool, faults, races, ticks⟩
  rcases races with _ | ⟨_ | _, _ | ⟨_ | _, rs⟩⟩ <;> rcases faults with _ | ⟨_ | _, fs⟩
  all_goals simp only [delivery_run, delivery, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_throw, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, FrFlow.Races.leftWins_exceptT,
    FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, FrFlow.runOnE_cut, FrFlow.runOnE_step,
    FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure, FrFlow.runOnE_each, PoolModel.Ops.take_onWorldE,
    PoolModel.Ops.give_onWorldE, LibraryModel.Ops.load_onWorldE, ClockModel.Ops.sleep_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races,
    PoolModel.take, PoolModel.give, LibraryModel.load, ClockModel.sleep, FrFlow.runOn_get, FrFlow.runOn_set,
    FrFlow.runOn_modify, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_map, ↓reduceIte, Bool.false_eq_true,
    ite_false, ite_true]
  all_goals first
    | (simp (config := { contextual := true }) [Lemmas.filter_mem_self, Lemmas.library_eta]; done)
    | (generalize hres : FrFlow.runOnE (List.mapM _ _) _ = res
       obtain ⟨bs, hbs, hinv⟩ : ∃ bs, res.1 = .ok bs ∧
           ((∃ keep : Notice → Bool, (res.2 : World).libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
           (∀ n ∈ lib.outbox, n ∈ (res.2 : World).libraryModel.outbox ∨ (n ∈ firstOfEach lib.outbox ∧ n ∈ mailbox (res.2 : World).mailerModel n.to)) ∧
           (∀ p, (∀ n ∈ firstOfEach lib.outbox, n.to ≠ p) → mailbox (res.2 : World).mailerModel p = mailbox boxes p) ∧
           (∀ n ∈ firstOfEach lib.outbox, mailbox (res.2 : World).mailerModel n.to = mailbox boxes n.to ∨
             mailbox (res.2 : World).mailerModel n.to = taken (mailbox boxes n.to) n)) := by
         rw [← hres]
         refine Lemmas.mapM_along _ (fun (done : List Notice) (s : World) =>
           ((∃ keep : Notice → Bool, s.libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
           (∀ n ∈ lib.outbox, n ∈ s.libraryModel.outbox ∨ (n ∈ done ∧ n ∈ mailbox s.mailerModel n.to)) ∧
           (∀ p, (∀ n ∈ done, n.to ≠ p) → mailbox s.mailerModel p = mailbox boxes p) ∧
           (∀ n ∈ done, mailbox s.mailerModel n.to = mailbox boxes n.to ∨
             mailbox s.mailerModel n.to = taken (mailbox boxes n.to) n))) _ ?_ _ ⟨⟨fun _ => true, by rw [List.filter_eq_self.2 (fun _ _ => rfl)]⟩, fun n hn => Or.inl hn,
           fun _ _ => rfl, fun _ hn => absurd hn List.not_mem_nil⟩
         intro done x rest s hsplit hD
         refine ⟨?_, delivery_kept lib boxes done rest x s _ hsplit hD ?_⟩
         all_goals rcases s with ⟨b, hk', c, l, p, fs, rs, ts⟩
         all_goals simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true]
         all_goals iterate 14 (all_goals (try (first
           | (rcases rs with _ | ⟨_ | _, rs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true])
           | (rcases fs with _ | ⟨_ | _, fs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true]))))
         all_goals (simp; done)
       rcases res with ⟨o, s'⟩
       simp only at hbs hinv
       subst hbs
       obtain ⟨⟨keep, hk⟩, h2, _, h4⟩ := hinv
       simp only [FrFlow.Clock.move]
       try (cases List.mapM id bs <;> simp only [])
       all_goals (try split)
       all_goals (try dsimp only)
       all_goals exact ⟨⟨⟨by rw [hk]; rw [Lemmas.filter_mem_filter], h2⟩, h4⟩, trivial⟩)

theorem bounded_tick (Y : World) (lo : Int) (h : lo ≤ Y.clockModel) : lo ≤ (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) Y).clockModel :=
  Int.le_trans h (tick_le Y)

theorem bounded_move (Y : World) (t lo : Int) (ht : Y.clockModel ≤ t) (h : lo ≤ Y.clockModel) :
    lo ≤ (FrFlow.Clock.move (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) t Y).clockModel := by
  unfold FrFlow.Clock.move
  simp only [↓reduceIte]
  omega

set_option maxHeartbeats 4000000 in
theorem run_clock (w : World) :
    (delivery_run w).2.housekeptModel = w.housekeptModel ∧ w.clockModel ≤ (delivery_run w).2.clockModel := by
  rcases w with ⟨boxes, hk, clock, lib, pool, faults, races, ticks⟩
  rcases races with _ | ⟨_ | _, _ | ⟨_ | _, rs⟩⟩ <;> rcases faults with _ | ⟨_ | _, fs⟩
  all_goals simp only [delivery_run, delivery, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_throw, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, FrFlow.Races.leftWins_exceptT,
    FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, FrFlow.runOnE_cut, FrFlow.runOnE_step,
    FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure, FrFlow.runOnE_each, PoolModel.Ops.take_onWorldE,
    PoolModel.Ops.give_onWorldE, LibraryModel.Ops.load_onWorldE, ClockModel.Ops.sleep_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races,
    PoolModel.take, PoolModel.give, LibraryModel.load, ClockModel.sleep, FrFlow.runOn_get, FrFlow.runOn_set,
    FrFlow.runOn_modify, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_map, ↓reduceIte, Bool.false_eq_true,
    ite_false, ite_true]
  all_goals first
    | (simp; done)
    | (generalize hres : FrFlow.runOnE (List.mapM _ _) _ = res
       obtain ⟨bs, hbs, hinv⟩ : ∃ bs, res.1 = .ok bs ∧ (World.housekeptModel res.2 = hk ∧
             clock ≤ World.clockModel res.2) := by
         rw [← hres]
         refine Lemmas.mapM_inv _ (fun (_ : List Notice) (s : World) => s.housekeptModel = hk ∧
           clock ≤ s.clockModel) ?_ _ [] _ ?_
         rotate_left
         · (try simp only [World.move_housekeptModel, World.ticked_housekeptModel])
           (repeat (first
               | assumption
               | trivial
               | rfl
               | exact ⟨_, rfl⟩
               | exact ⟨(), trivial⟩
               | (refine bounded_tick _ _ ?_)
               | (refine bounded_move _ _ _ (by first | (simp only []; omega) | omega | simp) ?_)
               | (apply And.intro)
               | omega
               | dsimp only))
         intro done x s hs
         rcases s with ⟨b, hk', c, l, p, fs, rs, ts⟩
         obtain ⟨rfl, hs1⟩ := hs
         simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true]
         iterate 14 (all_goals (try (first
           | (rcases rs with _ | ⟨_ | _, rs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true])
           | (rcases fs with _ | ⟨_ | _, fs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true]))))
         all_goals (try simp only [World.move_housekeptModel, World.ticked_housekeptModel])
         all_goals (repeat (first
             | assumption
             | trivial
             | rfl
             | exact ⟨_, rfl⟩
             | exact ⟨(), trivial⟩
             | (refine bounded_tick _ _ ?_)
             | (refine bounded_move _ _ _ (by first | (simp only []; omega) | omega | simp) ?_)
             | (apply And.intro)
             | omega
             | dsimp only))
       rcases res with ⟨o, s'⟩
       simp only at hbs hinv
       subst hbs
       simp only
       try (cases List.mapM id bs <;> simp only [])
       all_goals (try simp only [World.move_housekeptModel, World.ticked_housekeptModel, FrFlow.Clock.move, ↓reduceIte])
       all_goals (try split)
       all_goals (repeat (first
           | assumption
           | trivial
           | rfl
           | exact ⟨_, rfl⟩
           | exact ⟨(), trivial⟩
           | (refine bounded_tick _ _ ?_)
           | (refine bounded_move _ _ _ (by first | (simp only []; omega) | omega | simp) ?_)
           | (apply And.intro)
           | omega
           | dsimp only)))
    | ((try simp only [World.move_housekeptModel, World.ticked_housekeptModel]); (repeat (first
           | assumption
           | trivial
           | rfl
           | exact ⟨_, rfl⟩
           | exact ⟨(), trivial⟩
           | (refine bounded_tick _ _ ?_)
           | (refine bounded_move _ _ _ (by first | (simp only []; omega) | omega | simp) ?_)
           | (apply And.intro)
           | omega
           | dsimp only)); done)



/-- A run of housekeeping leaves nothing ended as of the time it ran: tidying keeps only the documents not gone and
the invitations open, chasing only the requests pending, each reminded once it is due. -/
theorem housekept_nothingEnded (lib : Library) (t : Int) :
    trashNotGoneAtHousekeeping (housekeptAt warnCode (chaseCode (isPendingCode 604800) (reminderDueCode 172800)) forgetCode (tidyCode (goneCode 2592000) inForceCode (isOpenCode 604800)) recordCode lib t) t ∧
      invitationsOpenAtHousekeeping (housekeptAt warnCode (chaseCode (isPendingCode 604800) (reminderDueCode 172800)) forgetCode (tidyCode (goneCode 2592000) inForceCode (isOpenCode 604800)) recordCode lib t) t ∧
      requestsPendingAtHousekeeping (housekeptAt warnCode (chaseCode (isPendingCode 604800) (reminderDueCode 172800)) forgetCode (tidyCode (goneCode 2592000) inForceCode (isOpenCode 604800)) recordCode lib t) t ∧
      remindedAtHousekeeping (housekeptAt warnCode (chaseCode (isPendingCode 604800) (reminderDueCode 172800)) forgetCode (tidyCode (goneCode 2592000) inForceCode (isOpenCode 604800)) recordCode lib t) t := by
  obtain ⟨hd, hi, hq⟩ := housekept_parts (isPendingCode 604800) (reminderDueCode 172800) (goneCode 2592000)
    inForceCode (isOpenCode 604800) lib t
  refine ⟨fun doc hdoc a ha => ?_, fun i hin => ?_, fun q hq' => ?_, fun q hq' => ?_⟩
  · rw [hd] at hdoc
    simp [tidyCode, goneCode] at hdoc
    have := hdoc.2 a ha
    omega
  · rw [hi] at hin
    simp only [tidyCode, List.mem_filter] at hin
    exact @of_decide_eq_true (isOpenCode 604800 i t) (propDecidable _) hin.2
  · rw [hq] at hq'
    simp only [chaseCode, List.mem_map, List.mem_filter] at hq'
    obtain ⟨q₀, ⟨_, hp⟩, rfl⟩ := hq'
    have hp' : t < q₀.asked + 604800 := @of_decide_eq_true (isPendingCode 604800 q₀ t) (propDecidable _) hp
    unfold chased
    by_cases hdue : reminderDueCode 172800 q₀ t ∧ ¬q₀.reminded
    · rw [if_pos hdue]
      exact hp'
    · rw [if_neg hdue]
      exact hp'
  · rw [hq] at hq'
    simp only [chaseCode, List.mem_map, List.mem_filter] at hq'
    obtain ⟨q₀, ⟨_, hp⟩, rfl⟩ := hq'
    unfold chased
    by_cases hdue : reminderDueCode 172800 q₀ t ∧ ¬q₀.reminded
    · rw [if_pos hdue]
      exact Or.inl trivial
    · rw [if_neg hdue]
      by_cases hr : q₀.reminded
      · exact Or.inl hr
      · exact Or.inr (Classical.byContradiction fun hc => hdue ⟨by simp only [reminderDueCode]; omega, hr⟩)


end Sharing.Lemmas
