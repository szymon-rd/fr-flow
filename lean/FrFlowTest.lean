import FrFlow

/-! Examples of the kernel's library lemmas (not part of the `FrFlow` library target).
Check with `lake env lean FrFlowTest.lean` from `lean/`. -/

set_option autoImplicit false

namespace FrFlowTest

/-! ## Machines -/

/-- A counter, abstracted by its parity. -/
def count (n : Nat) (k : Nat) : Nat := n + k
def parity (n : Nat) : Bool := n % 2 == 1
def flip (b : Bool) (k : Nat) : Bool := if k % 2 == 1 then !b else b

example (es : List Nat) : parity (es.foldl count 0) = es.foldl flip false :=
  FrFlow.simulates rfl (fun s k => by unfold parity count flip; split <;> grind) es

example : ∀ es : List Nat, parity (es.foldl count 0) = es.foldl flip false := by
  apply FrFlow.simulates
  · rfl
  · intro s k; unfold parity count flip; split <;> grind

/-- The step mirrors the abstract step only on states meeting an invariant (even numbers). -/
def bump (n : Nat) (_ : Unit) : Nat := n + 2
def half (n : Nat) : Nat := (n + 1) / 2

example (es : List Unit) : half (es.foldl bump 0) = es.foldl (fun a _ => a + 1) 0 :=
  FrFlow.simulates_of_inv (inv := fun n => n % 2 = 0) rfl rfl
    (fun s _ h => by unfold bump; omega) (fun s _ h => by unfold half bump; omega) es

/-- Relational: two counters stay `≤`. -/
example (es : List Nat) : es.foldl (fun n k => n + k) 0 ≤ es.foldl (fun n k => n + 2 * k) 1 :=
  FrFlow.simulates_rel (R := (· ≤ ·)) (by decide) (fun _ _ _ h => by omega) es

/-- History: sessions are users signed in; after a history, a user has a session exactly when
they signed in and did not sign out since (the last event about them is a sign-in). -/
inductive Ev | signIn (u : Nat) | signOut (u : Nat)

def stepS (s : Nat → Bool) : Ev → (Nat → Bool)
  | .signIn u => fun v => if v = u then true else s v
  | .signOut u => fun v => if v = u then false else s v

def about (u : Nat) : Ev → Bool
  | .signIn v => v == u
  | .signOut v => v == u

def active (es : List Ev) (u : Nat) : Bool :=
  match (es.filter (about u)).getLast? with
  | some (.signIn _) => true
  | _ => false

example (es : List Ev) : es.foldl stepS (fun _ => false) = active es := by
  apply FrFlow.tracks_eq (α := id)
  · rfl
  · intro s es e h
    simp only [id] at *
    subst h
    funext v
    cases e <;> simp [stepS, active, about, List.filter_append] <;> split <;> grind

/-- `tracks` with an invariant in the relation. -/
example (es : List Nat) : es.foldl (· + ·) 0 = es.sum ∧ True :=
  FrFlow.tracks (R := fun s es => s = es.sum ∧ True) ⟨rfl, trivial⟩
    (fun s es e ⟨h, _⟩ => ⟨by simp [h], trivial⟩) es

example (es : List Nat) (e : Nat) : (es ++ [e]).foldl count 0 = count (es.foldl count 0) e := by
  rw [FrFlow.run_snoc]

/-! ## Lists -/

example (l : List Nat) :
    (l.filter (fun x => x % 2 == 0)).filter (fun x => x % 4 == 0) = l.filter (fun x => x % 4 == 0) :=
  FrFlow.filter_filter_of_imp l (fun x h => by simp at *; omega)

example (l : List Nat) :
    (l.filter (fun x => x % 4 == 0)).filter (fun x => x % 2 == 0) = l.filter (fun x => x % 4 == 0) :=
  FrFlow.filter_filter_of_imp' l (fun x h => by simp at *; omega)

/-- Sessions with distinct tokens: two sessions with the same token are the same session. -/
structure Session where
  token : Nat
  user : Nat

example (ss : List Session) (h : (ss.map Session.token).Nodup) (a b : Session)
    (ha : a ∈ ss) (hb : b ∈ ss) (ht : a.token = b.token) : a.user = b.user := by
  rw [FrFlow.eq_of_nodup_map h ha hb ht]

example (ss : List Session) (h : (ss.map Session.token).Nodup) (u : Nat) :
    ((ss.filter (fun s => s.user != u)).map Session.token).Nodup :=
  FrFlow.nodup_map_filter _ h

example (ss : List Session) (h : (ss.map Session.token).Nodup) (s : Session)
    (fresh : ∀ t ∈ ss, t.token ≠ s.token) : ((ss ++ [s]).map Session.token).Nodup :=
  FrFlow.nodup_map_snoc h fresh

end FrFlowTest

/-! ## frflow_intro -/

set_option linter.unusedVariables false in
def Obl (P : Nat → Prop) : Prop := ∀ (x y : Nat) (h_Pos : 0 < x) (h_Le : x ≤ y), P y

/-- The binders come in by their names, whatever their position. -/
example : Obl (fun y => 0 < y) := by
  unfold Obl
  frflow_intro
  exact Nat.lt_of_lt_of_le h_Pos h_Le
