import FrFlowGen.Sharing.Domain

/-! Facts the sharing proofs share: an `if` that changed a value took its branch; what each request leaves of the
documents, the invitations and the requests; and that recording and announcing it touch only the log and the
outbox. A request is served, and housekeeping run, by the operations' code (`answered`, `servedByCode`, `housekept`:
the defines the programs call, each operation its code, which each operation's contract says it is). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Lemmas

/-- What a request leads to, each operation its code. -/
def answered (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) : Library :=
  afterRequest (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit) (inviteCode mayEdit)
    (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit) (restoreCode gone mayEdit) askCode
    (approveCode isPending mayEdit ownedBy) (declineCode mayEdit) (transferCode mayEdit) lib t r

/-- The library a request leaves, each operation its code: when it changed, recorded and announced. -/
def servedByCode (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) : Library :=
  served announceCode recordCode (shareCode mayEdit ownedBy) (unshareCode mayEdit ownedBy) (moveCode mayEdit)
    (inviteCode mayEdit) (acceptCode isOpen ownedBy) (withdrawCode mayEdit) (trashCode mayEdit)
    (restoreCode gone mayEdit) askCode (approveCode isPending mayEdit ownedBy) (declineCode mayEdit)
    (transferCode mayEdit) lib t r

/-- The library a run of housekeeping leaves at a moment, each operation its code. -/
def housekept (isPending reminderDue : AccessRequest → Int → Prop) (gone : Document → Int → Prop)
    (inForce : Share → Int → Prop) (isOpen : Invitation → Int → Prop) (lib : Library) (t : Int) : Library :=
  housekeptAt warnCode (chaseCode isPending reminderDue) forgetCode (tidyCode gone inForce isOpen) recordCode lib t

/-- An `if` whose value is not its `else` branch's took its `then` branch. -/
theorem changed {α : Type} {c : Prop} {inst : Decidable c} {a b : α} (h : ¬ (@ite α c inst a b = b)) : c :=
  Classical.byContradiction fun hn => h (ite_eq_right hn)

/-- A request served: as it was, or what its operation left, recorded and announced, which changes the documents,
the invitations, the requests and the shares no more. -/
theorem served_cases (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    servedByCode mayEdit ownedBy isOpen gone isPending lib t r = lib ∨
      ((servedByCode mayEdit ownedBy isOpen gone isPending lib t r).documents =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).documents ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).invitations =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).invitations ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).requests =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).requests ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).shares =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).shares) := by
  simp only [servedByCode, served, answered]
  split
  · exact Or.inr ⟨by simp [announceCode, recordCode], by simp [announceCode, recordCode],
      by simp [announceCode, recordCode], by simp [announceCode, recordCode]⟩
  · exact Or.inl rfl

/-- A document a request leaves is out of the trash, put there now, or in it since a time the library held. -/
theorem answered_documents (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    ∀ doc ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).documents,
      doc.trashed = none ∨ doc.trashed = some t ∨ ∃ x ∈ lib.documents, x.trashed = doc.trashed := by
  intro doc hd
  cases r <;> simp only [answered, afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
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
    ∀ i ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).invitations, i ∈ lib.invitations ∨ i.sent = t := by
  intro i hi
  cases r <;> simp only [answered, afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hi <;>
    (try split at hi) <;> (try split at hi) <;> simp_all [invitationsWithout, List.mem_filter]
  all_goals rcases hi with rfl | ⟨h, _⟩ <;> simp_all

/-- A request for access a request leaves is one the library held, or one made now and not reminded. -/
theorem answered_requests (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    ∀ q ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).requests,
      q ∈ lib.requests ∨ (q.asked = t ∧ ¬ q.reminded) := by
  intro q hq
  cases r <;> simp only [answered, afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hq <;>
    (try split at hq) <;> (try split at hq) <;> simp_all [requestsWithout, List.mem_filter]
  all_goals rcases hq with rfl | ⟨h, _⟩ <;> simp_all

/-- A request that changes the library is recorded at the end of the log, and announced in the outbox, in the same
step; one that does not leaves the library as it was. -/
theorem served_logged (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    servedByCode mayEdit ownedBy isOpen gone isPending lib t r = lib ∨
      ((servedByCode mayEdit ownedBy isOpen gone isPending lib t r).shares =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).shares ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).log =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).log ++
            [Entry.mk ((answered mayEdit ownedBy isOpen gone isPending lib t r).log.length : Int) t (Change.Made r)] ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).outbox =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).outbox ++
            noticesOf lib r (Entry.mk ((answered mayEdit ownedBy isOpen gone isPending lib t r).log.length : Int) t
              (Change.Made r))) := by
  simp only [servedByCode, served, answered]
  split
  · exact Or.inr ⟨by simp [announceCode, recordCode], by simp [announceCode, recordCode],
      by simp [announceCode, recordCode]⟩
  · exact Or.inl rfl

/-- The operations leave the log alone. -/
theorem answered_log (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    (answered mayEdit ownedBy isOpen gone isPending lib t r).log = lib.log := by
  cases r <;> simp only [answered, afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] <;> (try split) <;> (try split) <;> rfl

/-- The operations leave the outbox alone. -/
theorem answered_outbox (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) :
    (answered mayEdit ownedBy isOpen gone isPending lib t r).outbox = lib.outbox := by
  cases r <;> simp only [answered, afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] <;> (try split) <;> (try split) <;> rfl

/-- A share a request leaves is one the library held, or one the request made (as its log entry says). -/
theorem answered_shares (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
    (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)
    (lib : Library) (t : Int) (r : Request) (n : Int) :
    ∀ s ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).shares,
      s ∈ lib.shares ∨ makes (Entry.mk n t (Change.Made r)) s := by
  intro s hs
  cases r <;> simp only [answered, afterRequest, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
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
    (housekept isPending reminderDue gone inForce isOpen lib t).documents = (tidyCode gone inForce isOpen lib t).documents ∧
      (housekept isPending reminderDue gone inForce isOpen lib t).invitations =
        (tidyCode gone inForce isOpen lib t).invitations ∧
      (housekept isPending reminderDue gone inForce isOpen lib t).requests =
        (chaseCode isPending reminderDue (tidyCode gone inForce isOpen lib t) t).requests := by
  simp only [housekept, housekeptAt]
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

end Sharing.Lemmas
