import FrFlowGen.Sharing.Domain

/-! Facts the sharing proofs share: an `if` that changed a value took its branch; what each request leaves of the
documents, the invitations and the requests; and that recording and announcing it touch only the log and the
outbox. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Lemmas

/-- An `if` whose value is not its `else` branch's took its `then` branch. -/
theorem changed {α : Type} {c : Prop} {inst : Decidable c} {a b : α} (h : ¬ (@ite α c inst a b = b)) : c :=
  Classical.byContradiction fun hn => h (ite_eq_right hn)

/-- What clockNeverGoesBack asks of an event: a wait is of no time or more. -/
def forward : Event → Prop
  | Event.Waited d => (0 : Int) ≤ d
  | _ => True

section Answered
variable (mayEdit : Library → Int → PersonId → Target → Prop) (ownedBy : Library → Target → Grantee → Prop)
  (isOpen : Invitation → Int → Prop) (gone : Document → Int → Prop) (isPending : AccessRequest → Int → Prop)

/-- A request served: as it was, or what its operation left, recorded and announced, which changes the documents,
the invitations, the requests and the shares no more. -/
theorem served_cases (lib : Library) (t : Int) (r : Request) :
    servedByCode mayEdit ownedBy isOpen gone isPending lib t r = lib ∨
      ((servedByCode mayEdit ownedBy isOpen gone isPending lib t r).documents =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).documents ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).invitations =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).invitations ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).requests =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).requests ∧
        (servedByCode mayEdit ownedBy isOpen gone isPending lib t r).shares =
          (answered mayEdit ownedBy isOpen gone isPending lib t r).shares) := by
  simp only [servedByCode]
  split
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl rfl

/-- A document a request leaves is out of the trash, put there now, or in it since a time the library held. -/
theorem answered_documents (lib : Library) (t : Int) (r : Request) :
    ∀ doc ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).documents,
      doc.trashed = none ∨ doc.trashed = some t ∨ ∃ x ∈ lib.documents, x.trashed = doc.trashed := by
  intro doc hd
  cases r <;> simp only [answered, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted, handedOn] at hd <;>
    (try split at hd) <;> (try split at hd) <;> (try simp only [List.mem_map] at hd)
  all_goals first
    | exact Or.inr (Or.inr ⟨doc, hd, rfl⟩)
    | (obtain ⟨x, hx, rfl⟩ := hd; split <;> first | exact Or.inr (Or.inr ⟨x, hx, rfl⟩) | simp_all)
    | simp_all

/-- An invitation a request leaves is one the library held, or one sent now. -/
theorem answered_invitations (lib : Library) (t : Int) (r : Request) :
    ∀ i ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).invitations, i ∈ lib.invitations ∨ i.sent = t := by
  intro i hi
  cases r <;> simp only [answered, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hi <;>
    (try split at hi) <;> (try split at hi) <;> simp_all [invitationsWithout, List.mem_filter]
  all_goals rcases hi with rfl | ⟨h, _⟩ <;> simp_all

/-- A request for access a request leaves is one the library held, or one made now and not reminded. -/
theorem answered_requests (lib : Library) (t : Int) (r : Request) :
    ∀ q ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).requests,
      q ∈ lib.requests ∨ (q.asked = t ∧ ¬ q.reminded) := by
  intro q hq
  cases r <;> simp only [answered, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hq <;>
    (try split at hq) <;> (try split at hq) <;> simp_all [requestsWithout, List.mem_filter]
  all_goals rcases hq with rfl | ⟨h, _⟩ <;> simp_all

/-- A request that changes the library is recorded at the end of the log, and announced in the outbox, in the same
step; one that does not leaves the library as it was. -/
theorem served_logged (lib : Library) (t : Int) (r : Request) :
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
  simp only [servedByCode]
  split
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl rfl

/-- The operations leave the log alone. -/
theorem answered_log (lib : Library) (t : Int) (r : Request) :
    (answered mayEdit ownedBy isOpen gone isPending lib t r).log = lib.log := by
  cases r <;> simp only [answered, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] <;> (try split) <;> (try split) <;> rfl

/-- The operations leave the outbox alone. -/
theorem answered_outbox (lib : Library) (t : Int) (r : Request) :
    (answered mayEdit ownedBy isOpen gone isPending lib t r).outbox = lib.outbox := by
  cases r <;> simp only [answered, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] <;> (try split) <;> (try split) <;> rfl

/-- A share a request leaves is one the library held, or one the request made (as its log entry says). -/
theorem answered_shares (lib : Library) (t : Int) (r : Request) (n : Int) :
    ∀ s ∈ (answered mayEdit ownedBy isOpen gone isPending lib t r).shares,
      s ∈ lib.shares ∨ makes (Entry.mk n t (Change.Made r)) s := by
  intro s hs
  cases r <;> simp only [answered, shareCode, unshareCode, moveCode, inviteCode, acceptCode, withdrawCode, trashCode,
    restoreCode, askCode, approveCode, declineCode, transferCode, granted] at hs <;>
    (try split at hs) <;> (try split at hs) <;>
    simp_all [sharesWithout, List.mem_filter, makes, madeBy, ownersEdit]
  all_goals rcases hs with h | ⟨h, _⟩ <;> simp_all
  all_goals rename_i hq _
  all_goals have := List.find?_some hq
  all_goals simp_all

end Answered

/-- What a run of housekeeping leaves of the documents, the invitations and the requests is what tidying and chasing
leave of them: forgetting old entries, telling of ending shares and recording the run touch none of them. -/
theorem housekept_parts (isPending reminderDue : AccessRequest → Int → Prop) (gone : Document → Int → Prop)
    (inForce : Share → Int → Prop) (isOpen : Invitation → Int → Prop) (lib : Library) (t : Int) :
    (housekept isPending reminderDue gone inForce isOpen lib t).documents = (tidyCode gone inForce isOpen lib t).documents ∧
      (housekept isPending reminderDue gone inForce isOpen lib t).invitations =
        (tidyCode gone inForce isOpen lib t).invitations ∧
      (housekept isPending reminderDue gone inForce isOpen lib t).requests =
        (chaseCode isPending reminderDue (tidyCode gone inForce isOpen lib t) t).requests := by
  simp only [housekept]
  split
  · exact ⟨rfl, rfl, rfl⟩
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
theorem mailbox_with (boxes : List Mailbox) (q p : PersonId) (ns : List Notice) :
    mailbox (withMailbox boxes q ns) p = if p = q then ns else mailbox boxes p := by
  by_cases h : p = q
  · subst h; simp [mailbox, withMailbox]
  · have keep : List.find? (fun b => decide (b.person = p)) (List.filter (fun b => decide ¬b.person = q) boxes) =
        List.find? (fun b => decide (b.person = p)) boxes := by
      induction boxes with
      | nil => rfl
      | cons b bs ih =>
        by_cases hb : b.person = q
        · have hp : ¬ b.person = p := fun e => h (e ▸ hb)
          rw [List.filter_cons_of_neg (by simpa using hb), ih, List.find?_cons_of_neg (by simpa using hp)]
        · rw [List.filter_cons_of_pos (by simpa using hb), List.find?_cons, List.find?_cons, ih]
    have hq : ¬ q = p := fun e => h e.symm
    simp only [mailbox, withMailbox, List.find?_cons, hq, decide_false, h, ↓reduceIte, keep]

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
@[simp] theorem filter_mem_self {α : Type} (l : List α) {d : ∀ n, Decidable (n ∈ l)} :
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
@[simp] theorem library_eta (l : Library) :
    Library.mk l.documents l.folders l.teams l.shares l.invitations l.requests l.log l.outbox = l := rfl

end Sharing.Lemmas
