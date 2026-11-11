import FrFlowGen.Shop.Domain

/-! What the proofs of the shop share: an account's balance and a product's units over entries added, and what
solvent, stocked and orderly give. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Shop.Lemmas
open Shop

/-- A sum of postings' amounts from `z` is `z` and their sum from nothing. -/
theorem amounts_from (l : List Posting) (z : Int) :
    List.foldl (fun (sum : Int) (p : Posting) => sum + p.amount) z l =
      z + List.foldl (fun (sum : Int) (p : Posting) => sum + p.amount) 0 l := by
  induction l generalizing z with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (z + p.amount), ih (0 + p.amount)]
    omega

/-- A sum of movements' units from `z` is `z` and their sum from nothing. -/
theorem units_from (l : List Movement) (z : Int) :
    List.foldl (fun (sum : Int) (m : Movement) => sum + m.units) z l =
      z + List.foldl (fun (sum : Int) (m : Movement) => sum + m.units) 0 l := by
  induction l generalizing z with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldl_cons]
    rw [ih (z + m.units), ih (0 + m.units)]
    omega

/-- An account's balance over postings added is its balance before and its balance in those added. -/
theorem balance_append (l m : List Posting) (a : String) : balance (l ++ m) a = balance l a + balance m a := by
  unfold balance
  rw [List.filter_append, List.foldl_append, amounts_from]

/-- A product's units over movements added are its units before and its units in those added. -/
theorem available_append (l m : List Movement) (s : String) :
    available (l ++ m) s = available l s + available m s := by
  unfold available
  rw [List.filter_append, List.foldl_append, units_from]

/-- What a charge's two postings change of an account's balance. -/
theorem balance_charged (o : Order) (a : String) :
    balance [Posting.mk o.id_ o.customer ((0 : Int) - o.amount), Posting.mk o.id_ "shop" o.amount] a =
      (if o.customer = a then -o.amount else 0) + (if "shop" = a then o.amount else 0) := by
  unfold balance
  by_cases h1 : o.customer = a <;> by_cases h2 : "shop" = a <;> simp [List.filter, h1, h2]

/-- What one movement changes of a product's units. -/
theorem available_one (m : Movement) (s : String) : available [m] s = if m.sku = s then m.units else 0 := by
  unfold available
  by_cases h : m.sku = s <;> simp [List.filter, h]

/-- In solvent books every account's balance is at least nothing, those with no posting too. -/
theorem balance_nonneg (b : Books) (h : solvent b) (a : String) : 0 ≤ balance b.postings a := by
  by_cases hex : ∃ p ∈ b.postings, p.account = a
  · obtain ⟨p, hp, rfl⟩ := hex
    exact h p hp
  · have none : List.filter (fun p => decide (p.account = a)) b.postings = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      simp only [decide_eq_true_eq]
      exact fun h' => hex ⟨p, hp, h'⟩
    unfold balance
    rw [none]
    simp

/-- In a stocked warehouse every product has at least no units to sell, those with no movement too. -/
theorem available_nonneg (s : Stock) (h : stocked s) (sku : String) : 0 ≤ available s.movements sku := by
  by_cases hex : ∃ m ∈ s.movements, m.sku = sku
  · obtain ⟨m, hm, rfl⟩ := hex
    exact h m hm
  · have none : List.filter (fun m => decide (m.sku = sku)) s.movements = [] := by
      rw [List.filter_eq_nil_iff]
      intro m hm
      simp only [decide_eq_true_eq]
      exact fun h' => hex ⟨m, hm, h'⟩
    unfold available
    rw [none]
    simp

/-- Books whose postings are solvent books' and a covered charge's two are solvent. -/
theorem charged_solvent (b after : Books) (o : Order) (hpos : 0 < o.amount) (h : solvent b)
    (hc : o.amount ≤ balance b.postings o.customer)
    (hp : after.postings = b.postings ++
      [Posting.mk o.id_ o.customer ((0 : Int) - o.amount), Posting.mk o.id_ "shop" o.amount]) :
    solvent after := by
  intro p _
  rw [hp, balance_append, balance_charged]
  have held := balance_nonneg b h p.account
  by_cases h1 : o.customer = p.account <;> by_cases h2 : "shop" = p.account <;>
    simp only [h1, h2, ite_true, ite_false]
  all_goals first
    | (rw [h1] at hc; omega)
    | omega

/-- A stock whose movements are a stocked one's and one that takes no units is stocked. -/
theorem added_stocked (s after : Stock) (m : Movement) (hpos : 0 ≤ m.units) (h : stocked s)
    (hp : after.movements = s.movements ++ [m]) : stocked after := by
  intro x _
  rw [hp, available_append, available_one]
  have held := available_nonneg s h x.sku
  by_cases h1 : m.sku = x.sku <;> simp only [h1, ite_true, ite_false] <;> omega

/-- Books with solvent books' postings are solvent. -/
theorem same_postings_solvent (b after : Books) (h : solvent b) (hp : after.postings = b.postings) :
    solvent after := by
  intro p hm
  rw [hp] at hm ⊢
  exact h p hm

/-- In orderly books an order whose payment is not claimed has no posting. -/
theorem unclaimed_unmade (b : Books) (h : orderly b) (r : String) (hr : r ∉ b.claimed) : made b.postings r = [] := by
  unfold made
  rw [List.filter_eq_nil_iff]
  intro p hp
  simp only [decide_eq_true_eq]
  exact fun h' => hr (h' ▸ h p hp)

/-- An order placed is registered afterwards, however it ended: registering marks it, and recording an end
keeps the orders registered. -/
theorem placed_is_registered (register : Journal → String → (Prop × Journal))
    (reserve : Stock → Order → (Prop × Stock)) (settle : Journal → Settlement → (Unit × Journal))
    (charge : Books → Order → (Charged × Books)) (release : Stock → Order → (Unit × Stock))
    (hstays : ∀ (journal : Journal) (order other : String),
      (other = order ∨ other ∈ journal.registered) → other ∈ (register journal order).2.registered)
    (hsettle : ∀ (journal : Journal) (s : Settlement), (settle journal s).2.registered = journal.registered)
    (shop : ShopState) (o : Order) :
    o.id_ ∈ (placeCode register reserve settle charge release shop o).2.journal.registered := by
  have marked := hstays shop.journal o.id_ o.id_ (Or.inl rfl)
  unfold placeCode
  by_cases hmine : (register shop.journal o.id_).1
  · by_cases hres : (reserve shop.stock o).1
    · by_cases hch : (charge shop.books o).1 = Charged.Done
      · simp only [hmine, hres, hch, not_true_eq_false, ite_true, ite_false, hsettle]
        exact marked
      · simp only [hmine, hres, hch, not_true_eq_false, ite_false, hsettle]
        exact marked
    · simp only [hmine, hres, not_true_eq_false, not_false_eq_true, ite_true, ite_false, hsettle]
      exact marked
  · simp only [hmine, not_false_eq_true, ite_true]
    exact marked

/-- Placing an order whose registration is lost answers a duplicate and leaves the shop as the registration
left it. -/
theorem lost_place (register : Journal → String → (Prop × Journal))
    (reserve : Stock → Order → (Prop × Stock)) (settle : Journal → Settlement → (Unit × Journal))
    (charge : Books → Order → (Charged × Books)) (release : Stock → Order → (Unit × Stock))
    (shop : ShopState) (o : Order) (lost : ¬(register shop.journal o.id_).1) :
    placeCode register reserve settle charge release shop o =
      (Placement.Duplicate, { shop with journal := (register shop.journal o.id_).2 }) := by
  unfold placeCode
  simp only [lost, not_false_eq_true, ite_true]

/-- What other calls keep, the shop a step starts from has: what the schedule says they left before step `k`,
when it is one they may leave (`others`), else the shop the call last saw. -/
theorem admitted_keeps (o : Order) (between : Int → Option ShopState) (P : ShopState → Prop)
    (hrely : ∀ b s, P b → others o b s → P s) (k : Int) (b : ShopState) (hb : P b) :
    P (if others o b (Option.getD (between k) b) then Option.getD (between k) b else b) := by
  by_cases h : others o b (Option.getD (between k) b)
  · simp only [h, ite_true]
    exact hrely b _ hb h
  · simp only [h, ite_false]
    exact hb

/-- Placing an order among other calls, step by step. `P` is kept throughout, `A` until the payment is claimed,
`B` from a claim won until the charge: other calls keep each, the shop has `P` and `A` at the start, and each of
the store's transactions, made from a shop that has what holds at its point, makes a step `Q` holds of and leaves
a shop that has what holds after it. Then `Q` holds of every step, on every schedule. -/
theorem every_step (register : Journal → String → (Prop × Journal)) (hold : Stock → Order → (Prop × Stock))
    (settle : Journal → Settlement → (Unit × Journal)) (claim : Books → String → (Prop × Books))
    (chargeIfCovered : Books → Order → (Prop × Books)) (putBack : Stock → Order → (Unit × Stock))
    (o : Order) (between : Int → Option ShopState) (P A B : ShopState → Prop) (Q : ShopState × ShopState → Prop)
    (hP : ∀ b s, P b → others o b s → P s) (hA : ∀ b s, A b → others o b s → A s)
    (hB : ∀ b s, B b → others o b s → B s)
    (hregister : ∀ b, P b → A b → Q (b, { b with journal := (register b.journal o.id_).2 }) ∧
      P { b with journal := (register b.journal o.id_).2 } ∧ A { b with journal := (register b.journal o.id_).2 })
    (hhold : ∀ b, P b → A b → Q (b, { b with stock := (hold b.stock o).2 }) ∧
      P { b with stock := (hold b.stock o).2 } ∧ A { b with stock := (hold b.stock o).2 })
    (hsettle : ∀ b st, P b → Q (b, { b with journal := (settle b.journal st).2 }) ∧
      P { b with journal := (settle b.journal st).2 })
    (hclaim : ∀ b, P b → A b → Q (b, { b with books := (claim b.books o.id_).2 }) ∧
      P { b with books := (claim b.books o.id_).2 } ∧
      ((claim b.books o.id_).1 → B { b with books := (claim b.books o.id_).2 }))
    (hcharge : ∀ b, P b → B b → Q (b, { b with books := (chargeIfCovered b.books o).2 }) ∧
      P { b with books := (chargeIfCovered b.books o).2 })
    (hput : ∀ b, P b → Q (b, { b with stock := (putBack b.stock o).2 }) ∧
      P { b with stock := (putBack b.stock o).2 })
    (shop : ShopState) (hP0 : P shop) (hA0 : A shop) :
    ∀ step ∈ (placeAmongOthersCode register hold settle claim chargeIfCovered putBack shop between o).2,
      Q step := by
  intro step hstep
  unfold placeAmongOthersCode at hstep
  extract_lets did s1 tr1 mine seen2 n2 did1 s2 tr2 reserved seen3 n3 didR sR trR did2 s3 tr3 won seen4 n4 did3
    s4 tr4 paid afterP charged seen5 n5 didC sC trC didB s5 tr5 seen6 n6 did6 s6 tr6 after1 after2 after3 at hstep
  have q1 := hregister shop hP0 hA0
  by_cases hmine : mine
  case neg =>
    simp only [after3, hmine, not_false_eq_true, ite_true, tr1, List.nil_append, List.mem_singleton] at hstep
    subst hstep
    exact q1.1
  have q2 := hhold n2 (admitted_keeps o between P hP 2 s1 q1.2.1) (admitted_keeps o between A hA 2 s1 q1.2.2)
  have p3 : P n3 := admitted_keeps o between P hP 3 s2 q2.2.1
  have a3 : A n3 := admitted_keeps o between A hA 3 s2 q2.2.2
  by_cases hres : reserved
  case neg =>
    have q3 := hsettle n3 (Settlement.mk o.id_ Status.Rejected) p3
    simp only [after3, after2, hmine, hres, not_true_eq_false, not_false_eq_true, ite_true, ite_false, trR, tr2,
      tr1, List.nil_append, List.mem_append, List.mem_singleton, or_assoc] at hstep
    rcases hstep with rfl | rfl | rfl
    · exact q1.1
    · exact q2.1
    · exact q3.1
  have q3 := hclaim n3 p3 a3
  by_cases hwon : won
  · have q4 := hcharge n4 (admitted_keeps o between P hP 4 s3 q3.2.1)
      (admitted_keeps o between B hB 4 s3 (q3.2.2 hwon))
    have e : afterP.2.1 = s4 := by simp only [afterP, hwon, not_true_eq_false, ite_false]
    have p5 : P n5 := admitted_keeps o between P hP 5 afterP.2.1 (by rw [e]; exact q4.2)
    by_cases hpaid : paid
    · have q5 := hsettle n5 (Settlement.mk o.id_ Status.Confirmed) p5
      simp only [after3, after2, after1, afterP, charged, hmine, hres, hwon, hpaid, not_true_eq_false, ite_true,
        ite_false, trC, tr4, tr3, tr2, tr1, List.nil_append, List.mem_append, List.mem_singleton, or_assoc]
        at hstep
      rcases hstep with rfl | rfl | rfl | rfl | rfl
      · exact q1.1
      · exact q2.1
      · exact q3.1
      · exact q4.1
      · exact q5.1
    · have q5 := hput n5 p5
      have q6 := hsettle n6 (Settlement.mk o.id_ Status.Rejected) (admitted_keeps o between P hP 6 s5 q5.2)
      simp only [after3, after2, after1, afterP, charged, hmine, hres, hwon, hpaid, not_true_eq_false, ite_true,
        ite_false, reduceCtorEq, tr6, tr5, tr4, tr3, tr2, tr1, List.nil_append, List.mem_append,
        List.mem_singleton, or_assoc] at hstep
      rcases hstep with rfl | rfl | rfl | rfl | rfl | rfl
      · exact q1.1
      · exact q2.1
      · exact q3.1
      · exact q4.1
      · exact q5.1
      · exact q6.1
  · have e : afterP.2.1 = s3 := by simp only [afterP, hwon, not_false_eq_true, ite_true]
    have p5 : P n5 := admitted_keeps o between P hP 5 afterP.2.1 (by rw [e]; exact q3.2.1)
    have q5 := hput n5 p5
    have q6 := hsettle n6 (Settlement.mk o.id_ Status.Rejected) (admitted_keeps o between P hP 6 s5 q5.2)
    simp only [after3, after2, after1, afterP, charged, hmine, hres, hwon, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, reduceCtorEq, tr6, tr5, tr3, tr2, tr1, List.nil_append, List.mem_append,
      List.mem_singleton, or_assoc] at hstep
    rcases hstep with rfl | rfl | rfl | rfl | rfl
    · exact q1.1
    · exact q2.1
    · exact q3.1
    · exact q5.1
    · exact q6.1

end Shop.Lemmas
