import FrFlowGen.Payments.Domain

/-! What applying a payment does to a ledger: facts about the domain's words, used by the nodes' proofs.
    A step `f` on accounts stands for the one `applied` maps over them: it keeps ids, takes `amt` from the
    account `src`, adds it to the account `dst`, and leaves every other account as it is. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
noncomputable section
open Classical

namespace Payments.Lemmas

/-- A balance summed over accounts none of which has the id is what it started as. -/
theorem bal_skip (i : String) : ∀ (xs : List Account) (acc : Int), (∀ b ∈ xs, ¬ b.id_ = i) →
    List.foldl (fun (sum : Int) (a : Account) => if a.id_ = i then sum + a.balance else sum) acc xs = acc := by
  intro xs
  induction xs with
  | nil => intro acc _; rfl
  | cons b t ih =>
    intro acc h
    have hb : ¬ b.id_ = i := h b (List.mem_cons_self ..)
    simp only [List.foldl_cons, hb, if_false]
    exact ih acc (fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- Among accounts of distinct ids, the balance of an account's id is that account's balance. -/
theorem bal_of_mem : ∀ (xs : List Account) (acc : Int) (a : Account),
    List.Pairwise (fun (x : Account) (y : Account) => ¬ x.id_ = y.id_) xs → a ∈ xs →
    List.foldl (fun (sum : Int) (b : Account) => if b.id_ = a.id_ then sum + b.balance else sum) acc xs
      = acc + a.balance := by
  intro xs
  induction xs with
  | nil => intro acc a _ h; cases h
  | cons b t ih =>
    intro acc a hp ha
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with hab | hat
    · subst hab
      simp only [List.foldl_cons, if_true]
      exact bal_skip a.id_ t (acc + a.balance) (fun c hc h => hp.1 c hc h.symm)
    · have hb : ¬ b.id_ = a.id_ := hp.1 a hat
      simp only [List.foldl_cons, hb, if_false]
      exact ih acc a hp.2 hat

/-- A step that keeps ids keeps them distinct. -/
theorem distinct_map (f : Account → Account) (hid : ∀ a, (f a).id_ = a.id_) (xs : List Account)
    (hp : List.Pairwise (fun (x : Account) (y : Account) => ¬ x.id_ = y.id_) xs) :
    List.Pairwise (fun (x : Account) (y : Account) => ¬ x.id_ = y.id_) (List.map f xs) := by
  induction xs with
  | nil => simp
  | cons b t ih =>
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih hp.2⟩
    intro c hc
    rcases List.mem_map.mp hc with ⟨d, hd, rfl⟩
    rw [hid, hid]
    exact hp.1 d hd

/-- A balance of an id the step leaves alone is the same after it. -/
theorem bal_other (f : Account → Account) (i : String) (hid : ∀ a, (f a).id_ = a.id_)
    (hsame : ∀ a, a.id_ = i → (f a).balance = a.balance) : ∀ (xs : List Account) (acc : Int),
    List.foldl (fun (sum : Int) (a : Account) => if a.id_ = i then sum + a.balance else sum) acc (List.map f xs)
      = List.foldl (fun (sum : Int) (a : Account) => if a.id_ = i then sum + a.balance else sum) acc xs := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons b t ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons, hid]
    by_cases hb : b.id_ = i
    · simp only [hb, if_true, hsame b hb]; exact ih _
    · simp only [hb, if_false]; exact ih _

/-- A sum of balances started higher ends higher by as much. -/
theorem sum_shift : ∀ (xs : List Account) (acc c : Int),
    List.foldl (fun (sum : Int) (a : Account) => sum + a.balance) (acc + c) xs
      = List.foldl (fun (sum : Int) (a : Account) => sum + a.balance) acc xs + c := by
  intro xs
  induction xs with
  | nil => intro acc c; rfl
  | cons b t ih =>
    intro acc c
    simp only [List.foldl_cons]
    have h : acc + c + b.balance = acc + b.balance + c := by omega
    rw [h]; exact ih _ _

/-- The sum of balances after the step: `amt` less for an account `src` among them, `amt` more for an account
    `dst`, among accounts of distinct ids. -/
theorem sum_map (f : Account → Account) (src dst : String) (amt : Int) (hne : ¬ dst = src)
    (hid : ∀ a, (f a).id_ = a.id_) (hsrc : ∀ a, a.id_ = src → (f a).balance = a.balance - amt)
    (hdst : ∀ a, a.id_ = dst → (f a).balance = a.balance + amt)
    (hoth : ∀ a, ¬ a.id_ = src → ¬ a.id_ = dst → (f a).balance = a.balance) :
    ∀ (xs : List Account) (acc : Int), List.Pairwise (fun (x : Account) (y : Account) => ¬ x.id_ = y.id_) xs →
    List.foldl (fun (sum : Int) (a : Account) => sum + a.balance) acc (List.map f xs)
      = List.foldl (fun (sum : Int) (a : Account) => sum + a.balance) acc xs
        - (if ∃ a ∈ xs, a.id_ = src then amt else 0) + (if ∃ a ∈ xs, a.id_ = dst then amt else 0) := by
  intro xs
  induction xs with
  | nil => intro acc _; simp
  | cons b t ih =>
    intro acc hp
    rw [List.pairwise_cons] at hp
    have iht := ih (acc + (f b).balance) hp.2
    simp only [List.map_cons, List.foldl_cons]
    rw [iht]
    by_cases hbs : b.id_ = src
    · have hnot : ¬ ∃ a ∈ t, a.id_ = src := fun ⟨a, ha, h⟩ => hp.1 a ha (hbs.trans h.symm)
      have hbd : ¬ b.id_ = dst := fun h => hne (h.symm.trans hbs)
      have e1 : (∃ a ∈ b :: t, a.id_ = src) := ⟨b, List.mem_cons_self .., hbs⟩
      have e2 : (∃ a ∈ b :: t, a.id_ = dst) ↔ (∃ a ∈ t, a.id_ = dst) := by
        constructor
        · rintro ⟨a, ha, h⟩
          rcases List.mem_cons.mp ha with rfl | hat
          · exact absurd h hbd
          · exact ⟨a, hat, h⟩
        · rintro ⟨a, ha, h⟩; exact ⟨a, List.mem_cons_of_mem _ ha, h⟩
      rw [if_neg hnot, if_pos e1, hsrc b hbs]
      by_cases hd : ∃ a ∈ t, a.id_ = dst
      · rw [if_pos hd, if_pos (e2.mpr hd)]
        have := sum_shift t (acc + b.balance) (-amt)
        have h2 : acc + (b.balance - amt) = acc + b.balance + -amt := by omega
        rw [h2, this]; omega
      · rw [if_neg hd, if_neg (fun h => hd (e2.mp h))]
        have := sum_shift t (acc + b.balance) (-amt)
        have h2 : acc + (b.balance - amt) = acc + b.balance + -amt := by omega
        rw [h2, this]; omega
    · have e1 : (∃ a ∈ b :: t, a.id_ = src) ↔ (∃ a ∈ t, a.id_ = src) := by
        constructor
        · rintro ⟨a, ha, h⟩
          rcases List.mem_cons.mp ha with rfl | hat
          · exact absurd h hbs
          · exact ⟨a, hat, h⟩
        · rintro ⟨a, ha, h⟩; exact ⟨a, List.mem_cons_of_mem _ ha, h⟩
      by_cases hbd : b.id_ = dst
      · have hnot : ¬ ∃ a ∈ t, a.id_ = dst := fun ⟨a, ha, h⟩ => hp.1 a ha (hbd.trans h.symm)
        have e2 : (∃ a ∈ b :: t, a.id_ = dst) := ⟨b, List.mem_cons_self .., hbd⟩
        rw [if_neg hnot, if_pos e2, hdst b hbd]
        have := sum_shift t (acc + b.balance) amt
        have h2 : acc + (b.balance + amt) = acc + b.balance + amt := by omega
        by_cases hs : ∃ a ∈ t, a.id_ = src
        · rw [if_pos hs, if_pos (e1.mpr hs), h2, this]; omega
        · rw [if_neg hs, if_neg (fun h => hs (e1.mp h)), h2, this]; omega
      · have e2 : (∃ a ∈ b :: t, a.id_ = dst) ↔ (∃ a ∈ t, a.id_ = dst) := by
          constructor
          · rintro ⟨a, ha, h⟩
            rcases List.mem_cons.mp ha with rfl | hat
            · exact absurd h hbd
            · exact ⟨a, hat, h⟩
          · rintro ⟨a, ha, h⟩; exact ⟨a, List.mem_cons_of_mem _ ha, h⟩
        rw [hoth b hbs hbd]
        by_cases hs : ∃ a ∈ t, a.id_ = src <;> by_cases hd : ∃ a ∈ t, a.id_ = dst <;>
          simp only [hs, hd, e1, e2, if_true, if_false]

/-- The step `applied` maps over the accounts keeps ids. -/
theorem step_id (p : Payment) (a : Account) :
    (if (a.id_ = p.«from») then { a with balance := (a.balance - p.amount) }
      else (if (a.id_ = p.to) then { a with balance := (a.balance + p.amount) } else a) : Account).id_ = a.id_ := by
  by_cases h1 : a.id_ = p.«from»
  · simp [h1]
  · by_cases h2 : a.id_ = p.to
    · have h3 : ¬ p.to = p.«from» := h2 ▸ h1
      simp [h2, h3]
    · simp [h1, h2]

/-- Applying a payment keeps the accounts' ids distinct. -/
theorem applied_distinct (l : Ledger) (p : Payment) (hd : Payments.distinctIds l) :
    Payments.distinctIds (Payments.applied l p) := by
  simp only [Payments.distinctIds, Payments.applied] at hd ⊢
  exact distinct_map _ (step_id p) l.accounts hd

/-- Applying a payment between two different accounts that exist, of distinct ids, keeps the total. -/
theorem applied_total (l : Ledger) (p : Payment) (hd : Payments.distinctIds l) (hp : Payments.payable l p) :
    Payments.total (Payments.applied l p) = Payments.total l := by
  simp only [Payments.payable, Payments.owns, Payments.hasAccount] at hp
  obtain ⟨⟨⟨⟨⟨⟨a, ha, hai, _⟩, _⟩, _⟩, hne⟩, ⟨b, hb, hbi⟩⟩, _⟩ := hp
  simp only [Payments.distinctIds] at hd
  simp only [Payments.total, Payments.applied]
  have h := sum_map (fun a => (if (a.id_ = p.«from») then { a with balance := (a.balance - p.amount) }
      else (if (a.id_ = p.to) then { a with balance := (a.balance + p.amount) } else a)))
    p.«from» p.to p.amount hne (step_id p)
    (by intro x hx; simp [hx])
    (by intro x hx; simp [hx, hne])
    (by intro x h1 h2; simp [h1, h2]) l.accounts 0 hd
  rw [h, if_pos ⟨a, ha, hai⟩, if_pos ⟨b, hb, hbi⟩]; omega

/-- Applying a payment changes no balance but those of its two accounts. -/
theorem applied_other (l : Ledger) (p : Payment) (i : String) (h1 : ¬ i = p.«from») (h2 : ¬ i = p.to) :
    Payments.balanceOf (Payments.applied l p) i = Payments.balanceOf l i := by
  simp only [Payments.balanceOf, Payments.applied]
  exact bal_other _ i (step_id p) (by
    intro x hx
    have a1 : ¬ x.id_ = p.«from» := fun h => h1 (hx.symm.trans h)
    have a2 : ¬ x.id_ = p.to := fun h => h2 (hx.symm.trans h)
    simp [a1, a2]) l.accounts 0

/-- Among accounts of distinct ids, a ledger's balance of an account's id is that account's balance. -/
theorem balanceOf_mem (l : Ledger) (a : Account) (hd : Payments.distinctIds l) (ha : a ∈ l.accounts) :
    Payments.balanceOf l a.id_ = a.balance := by
  simp only [Payments.balanceOf, Payments.distinctIds] at hd ⊢
  have := bal_of_mem l.accounts 0 a hd ha
  omega

/-- Applying a payable payment to a ledger of distinct accounts makes it. -/
theorem applied_made (l : Ledger) (p : Payment) (hd : Payments.distinctIds l) (hp : Payments.payable l p) :
    Payments.made l (Payments.applied l p) p := by
  have hd' := applied_distinct l p hd
  simp only [Payments.payable, Payments.owns, Payments.hasAccount] at hp
  obtain ⟨⟨⟨⟨⟨⟨a, ha, hai, _⟩, _⟩, _⟩, hne⟩, ⟨b, hb, hbi⟩⟩, _⟩ := hp
  have hbn : ¬ b.id_ = p.«from» := fun h => hne (hbi.symm.trans h)
  have ma : ({ a with balance := a.balance - p.amount } : Account) ∈ (Payments.applied l p).accounts := by
    simp only [Payments.applied]
    exact List.mem_map.mpr ⟨a, ha, by simp [hai]⟩
  have mb : ({ b with balance := b.balance + p.amount } : Account) ∈ (Payments.applied l p).accounts := by
    simp only [Payments.applied]
    exact List.mem_map.mpr ⟨b, hb, by simp [hbi, hne]⟩
  have e1 := balanceOf_mem _ _ hd' ma
  have e2 := balanceOf_mem _ _ hd' mb
  have e3 := balanceOf_mem l a hd ha
  have e4 := balanceOf_mem l b hd hb
  simp only [hai] at e1 e3
  simp only [hbi] at e2 e4
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [e1, e3]
  · rw [e2, e4]
  · simp [Payments.hasPaid, Payments.applied]

/-- Applying a payable payment to a ledger of distinct accounts with no balance below zero leaves none below zero. -/
theorem applied_nonneg (l : Ledger) (p : Payment) (hn : Payments.noneNegative l) (hd : Payments.distinctIds l)
    (hp : Payments.payable l p) : Payments.noneNegative (Payments.applied l p) := by
  simp only [Payments.payable] at hp
  obtain ⟨⟨⟨⟨⟨_, hpos⟩, hcov⟩, hne⟩, _⟩, _⟩ := hp
  simp only [Payments.noneNegative, Payments.applied] at hn ⊢
  intro x hx
  rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
  have h0 := hn a ha
  by_cases h1 : a.id_ = p.«from»
  · have e := balanceOf_mem l a hd ha
    rw [h1] at e
    simp only [h1, if_true]
    show 0 ≤ a.balance - p.amount
    omega
  · by_cases h2 : a.id_ = p.to
    · simp only [h2, hne, if_false]
      show 0 ≤ a.balance + p.amount
      omega
    · simp only [h1, h2, if_false]; exact h0

end Payments.Lemmas
