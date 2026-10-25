import FrFlow.Flow

/-!
Branches at once. A flow's `parTupled` and `parTraverse` are read as their branches in turn; the
proof is asked that the branches commute (`commute_i`): either order gives the same results and
the same state. These lemmas are what such proofs, by hand or by automation, are made of: two
steps on parts of the state that neither reads nor writes of the other commute; reads commute;
commuting is symmetric; and a commuting pair can be swapped inside any flow around it, so that,
step by step, any order of whole branches gives what the written one gives.
-/

namespace FrFlow

/-- `x` and `y` commute: from every state, `x` then `y` and `y` then `x` give the same results and the same state. -/
def Commute {σ α β : Type} (x : StateM σ α) (y : StateM σ β) : Prop :=
  ∀ s, runOn (do let a ← x; let b ← y; pure (a, b)) s = runOn (do let b ← y; let a ← x; pure (a, b)) s

theorem Commute.symm {σ α β : Type} {x : StateM σ α} {y : StateM σ β} (h : Commute x y) : Commute y x := by
  intro s
  have e := h s
  simp only [runOn_bind, runOn_pure] at e ⊢
  exact Prod.ext (Prod.ext (congrArg (·.1.2) e).symm (congrArg (·.1.1) e).symm) (congrArg Prod.snd e).symm

/-- A step that gives a value and changes nothing commutes with every step. -/
theorem Commute.pure_left {σ α β : Type} (a : α) (y : StateM σ β) : Commute (pure a) y := by
  intro s; rfl

/-- Two reads commute. -/
theorem Commute.get_get {σ : Type} : Commute (get : StateM σ σ) (get : StateM σ σ) := by
  intro s; rfl

/-- Steps on two parts of the state commute when putting one part back leaves the other as it was, and the two puts
can be made in either order: what two fields of `World` are. -/
theorem Commute.within {σ τ υ α β : Type} (g₁ : σ → τ) (p₁ : σ → τ → σ) (g₂ : σ → υ) (p₂ : σ → υ → σ)
    (x : StateM τ α) (y : StateM υ β)
    (h₁ : ∀ s t, g₁ (p₂ s t) = g₁ s) (h₂ : ∀ s t, g₂ (p₁ s t) = g₂ s)
    (hp : ∀ s t u, p₁ (p₂ s u) t = p₂ (p₁ s t) u) :
    Commute (FrFlow.within g₁ p₁ x) (FrFlow.within g₂ p₂ y) := by
  intro s
  simp only [runOn_bind, runOn_pure, runOn_within, h₁, h₂, hp]

/-- A commuting pair swapped inside any flow around it: the flow before, the pair, and what follows of both results. -/
theorem Commute.swap {σ α β γ : Type} {x : StateM σ α} {y : StateM σ β} (h : Commute x y) (k : α → β → StateM σ γ) (s : σ) :
    runOn (do let a ← x; let b ← y; k a b) s = runOn (do let b ← y; let a ← x; k a b) s := by
  have e := h s
  simp only [runOn_bind, runOn_pure] at e ⊢
  have e1 := congrArg (·.1.1) e
  have e2 := congrArg (·.1.2) e
  have e3 := congrArg Prod.snd e
  simp only at e1 e2 e3
  rw [e1, e2, e3]

/-- `xs.mapM f` whose steps never fail and each keep `P` (which may read the elements still to come): the whole never
fails and keeps `P`. What the proof of a `parTraverse`, read in turn, rests on, beside the commutation of its branches. -/
theorem runOnE_mapM_keeps {σ ε α β : Type} (f : α → ExceptT ε (StateM σ) β) (P : List α → σ → Prop)
    (h : ∀ x rest s, P (x :: rest) s → ∃ b, (runOnE (f x) s).1 = .ok b ∧ P rest (runOnE (f x) s).2) :
    ∀ (xs : List α) (s : σ), P xs s → ∃ bs, (runOnE (xs.mapM f) s).1 = .ok bs ∧ P [] (runOnE (xs.mapM f) s).2 := by
  intro xs
  induction xs with
  | nil => intro s hs; exact ⟨[], rfl, hs⟩
  | cons x rest ih =>
    intro s hs
    obtain ⟨b, hb, hp⟩ := h x rest s hs
    rw [List.mapM_cons, runOnE_bind]
    generalize hr : runOnE (f x) s = r at hb hp
    rcases r with ⟨o, s'⟩
    simp only at hb hp
    subst hb
    obtain ⟨bs, hbs, hq⟩ := ih s' hp
    simp only
    rw [runOnE_bind]
    generalize hr2 : runOnE (List.mapM f rest) s' = r2 at hbs hq
    rcases r2 with ⟨o2, s''⟩
    simp only at hbs hq
    subst hbs
    exact ⟨b :: bs, rfl, hq⟩

/-- The same, of elements that each keep `P` from wherever they start: the run of `xs.mapM f`, its results dropped, gives
what `ok` says of every state `P` holds of. How a contract on a `parTraverse_`-like run is proven: one branch at a
time, from any state its invariant holds of. -/
theorem outcome_mapM_void {σ ε α β : Type} (f : α → ExceptT ε (StateM σ) β) (xs : List α) (P : σ → Prop)
    (ok : Unit → σ → Prop) (err : ε → σ → Prop)
    (h : ∀ x ∈ xs, ∀ s, P s → (runOnE (f x) s).1.toBool = true ∧ P (runOnE (f x) s).2)
    (hok : ∀ s, P s → ok () s) (s : σ) (hs : P s) :
    outcome ok err (runOnE (do let _ ← xs.mapM f; pure ()) s) := by
  obtain ⟨bs, hbs, hq⟩ := runOnE_mapM_keeps f (fun rest s => (∀ x ∈ rest, x ∈ xs) ∧ P s)
    (fun x rest s hp => by
      obtain ⟨hb, hp'⟩ := h x (hp.1 x (List.mem_cons_self ..)) s hp.2
      revert hb
      cases (runOnE (f x) s).1 with
      | ok b => exact fun _ => ⟨b, rfl, fun y hy => hp.1 y (List.mem_cons_of_mem _ hy), hp'⟩
      | error e => intro hb; simp [Except.toBool] at hb) xs s ⟨fun _ hx => hx, hs⟩
  rw [runOnE_bind]
  generalize hr : runOnE (xs.mapM f) s = r at hbs hq
  rcases r with ⟨o, s'⟩
  simp only at hbs hq
  subst hbs
  exact hok s' hq.2

end FrFlow
