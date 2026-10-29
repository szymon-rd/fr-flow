import FrFlowGen.Old.AccessExactly.Spec
import FrFlowGen.Old.AccessNeedsGrant.Spec
import FrFlowGen.Old.TokenNamesHolder.Spec
import FrFlowGen.Old.GrantLetsIn.Spec
import FrFlowGen.Old.DecisionContract.Spec
import FrFlowGen.Old.Domain
import FrFlowGen.Auth.accessExactly.Spec
import FrFlowGen.Auth.accessNeedsGrant.Spec
import FrFlowGen.Auth.tokenNamesHolder.Spec
import FrFlowGen.Auth.grantLetsIn.Spec
import FrFlowGen.Auth.decisionContract.Spec
import FrFlowGen.Auth.grantTable.Spec
import FrFlowGen.Auth.sessionTable.Spec
import FrFlowGen.Auth.requests.Spec
import Proofs.Auth.Lemmas

/-! No statement of auth is weakened by the port (ARCHITECTURE section 9, equivalence 4): each node's claim as
today's library stated it (`reference/auth`, put in namespace `Old` over the port's types) is equivalent to the
port's. Today's session table is a function from a token to the user it was issued to; the port's is the table
itself, a list of sessions each token issued once (`tokensIssuedOnce`), read as today's function by the user of the
session under the token (`asFunction`). Today's definitions of the purpose's words are the port's claims of one
equation, each equivalent to the word being today's define. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Port
open Auth

/-- The decision's step over one session, as its claim folds it. -/
def pick (grants : List Grant) (token : String) (path : Path) (found : Option UserId) (s : Session) :
    Option UserId :=
  if s.token = token ∧ grantFor grants s.user path then some s.user else found

/-- The session table as today's function: the user of the session under the token. -/
def asFunction (s : Sessions) (t : String) : Option UserId := (s.open.find? (fun x => decide (x.token = t))).map (·.user)

/-- With each token issued once, the table gives a user under a token exactly when a session of theirs is under it. -/
theorem asFunction_some (l : List Session) (hl : l.Pairwise (fun a b => ¬a.token = b.token)) (t : String)
    (u : UserId) : (l.find? (fun x => decide (x.token = t))).map (·.user) = some u ↔
      ∃ x ∈ l, x.token = t ∧ x.user = u := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    by_cases hy : y.token = t
    · simp only [List.find?_cons, hy, decide_true, Option.map_some, Option.some.injEq, List.mem_cons]
      constructor
      · intro h; exact ⟨y, Or.inl rfl, hy, h⟩
      · rintro ⟨x, rfl | hx, ht, hu⟩
        · exact hu
        · exact absurd (hy.trans ht.symm) (hl.1 x hx)
    · simp only [List.find?_cons, hy, decide_false, List.mem_cons]
      rw [ih hl.2]
      constructor
      · rintro ⟨x, hx, ht, hu⟩; exact ⟨x, Or.inr hx, ht, hu⟩
      · rintro ⟨x, rfl | hx, ht, hu⟩
        · exact absurd ht hy
        · exact ⟨x, hx, ht, hu⟩

theorem grantFor_iff (grants : List Grant) (u : UserId) (p : Path) : grantFor grants u p ↔ Grant.mk u p ∈ grants := by
  simp [grantFor]

/-- The decision's fold, read as today's: some user exactly when the session under the token names them with a
grant. -/
theorem fold_some (s : Sessions) (hs : tokensIssuedOnce s) (grants : List Grant) (t : String) (p : Path)
    (u : UserId) : s.open.foldl (pick grants t p) none = some u ↔
      asFunction s t = some u ∧ Grant.mk u p ∈ grants := by
  unfold asFunction
  rw [asFunction_some _ hs]
  constructor
  · intro h
    rcases Lemmas.found_from grants t p u _ _ h with h | ⟨x, hx, ht, hu, hg⟩
    · cases h
    · exact ⟨⟨x, hx, ht, hu⟩, (grantFor_iff _ _ _).1 hg⟩
  · rintro ⟨⟨x, hx, ht, rfl⟩, hg⟩
    exact Lemmas.finds grants t p _ none hs x hx ht ((grantFor_iff _ _ _).2 hg)

theorem accessExactly (access signedIn authorized) :
    Old.AccessExactly.claim UserId Path access signedIn authorized ↔
      Auth.accessExactly.claim access signedIn authorized := Iff.rfl

theorem accessNeedsGrant (admit grants) :
    Old.AccessNeedsGrant.claim admit grants ↔ Auth.accessNeedsGrant.claim admit grants := by
  simp only [Old.AccessNeedsGrant.claim, Auth.accessNeedsGrant.claim, grantFor_iff]
  constructor
  · intro h t p
    cases ha : admit t p with
    | none => trivial
    | some u => exact h t p u ha
  · intro h t p u ha
    have := h t p
    rw [ha] at this
    exact this

theorem tokenNamesHolder (admit) (s : Sessions) (hs : tokensIssuedOnce s) :
    Old.TokenNamesHolder.claim admit (asFunction s) ↔ Auth.tokenNamesHolder.claim admit s := by
  simp only [Old.TokenNamesHolder.claim, Auth.tokenNamesHolder.claim, issuedTo, asFunction]
  constructor
  · intro h _ t p
    cases ha : admit t p with
    | none => trivial
    | some u => exact (asFunction_some _ hs t u).1 (h t p u ha)
  · intro h t p u ha
    have := h hs t p
    rw [ha] at this
    exact (asFunction_some _ hs t u).2 this

theorem grantLetsIn (admit grants) (s : Sessions) (hs : tokensIssuedOnce s) :
    Old.GrantLetsIn.claim (asFunction s) grants admit ↔ Auth.grantLetsIn.claim s admit grants := by
  simp only [Old.GrantLetsIn.claim, Auth.grantLetsIn.claim, asFunction, grantFor_iff]
  constructor
  · intro h _ t p x hx ht hg
    exact h t p x.user ((asFunction_some _ hs t x.user).2 ⟨x, hx, ht, rfl⟩) hg
  · intro h t p u hu hg
    obtain ⟨x, hx, ht, rfl⟩ := (asFunction_some _ hs t u).1 hu
    exact h hs t p x hx ht hg

theorem decisionContract (admit grants) (s : Sessions) (hs : tokensIssuedOnce s) :
    Old.DecisionContract.claim (asFunction s) grants admit ↔ Auth.decisionContract.claim admit s grants := by
  unfold Old.DecisionContract.claim Old.DecisionContract.post Auth.decisionContract.claim
  constructor
  · intro h _ t p
    show admit t p = s.open.foldl (pick grants t p) none
    cases hf : s.open.foldl (pick grants t p) none with
    | some u => exact (h t p).2 u ((fold_some s hs grants t p u).1 hf).1 ((fold_some s hs grants t p u).1 hf).2
    | none =>
      cases ha : admit t p with
      | none => rfl
      | some u =>
        have := (fold_some s hs grants t p u).2 ((h t p).1 u ha)
        rw [hf] at this
        cases this
  · intro h t p
    have e : admit t p = s.open.foldl (pick grants t p) none := h hs t p
    refine ⟨fun u hu => ?_, fun u hu hg => ?_⟩
    · rw [e] at hu; exact (fold_some s hs grants t p u).1 hu
    · rw [e]; exact (fold_some s hs grants t p u).2 ⟨hu, hg⟩

/-- Today's definitions, each the port's claim of one equation: the word is today's define. -/
theorem grantTable (authorized grants) :
    Auth.grantTable.claim authorized grants ↔ ∀ u p, authorized u p = Old.authorized grants u p := by
  simp only [Auth.grantTable.claim, Old.authorized, grantFor_iff]

theorem sessionTable (signedIn) (s : Sessions) (hs : tokensIssuedOnce s) :
    Auth.sessionTable.claim signedIn s ↔ ∀ u, signedIn u = Old.signedIn (asFunction s) u := by
  unfold Auth.sessionTable.claim Old.signedIn
  have e : ∀ u, (∃ x ∈ s.open, x.user = u) = (∃ t, asFunction s t = some u) := fun u => by
    apply propext
    unfold asFunction
    constructor
    · rintro ⟨x, hx, hu⟩; exact ⟨x.token, (asFunction_some _ hs _ u).2 ⟨x, hx, rfl, hu⟩⟩
    · rintro ⟨t, ht⟩
      obtain ⟨x, hx, _, hu⟩ := (asFunction_some _ hs t u).1 ht
      exact ⟨x, hx, hu⟩
  simp only [e]
  exact ⟨fun h => h hs, fun h _ => h⟩

theorem requests (access admit) :
    Auth.requests.claim access admit ↔ ∀ u p, access u p = Old.access admit u p := by
  simp only [Auth.requests.claim, Old.access, Classical.not_forall, Classical.not_not]

end Port
