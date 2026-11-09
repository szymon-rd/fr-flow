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

/-! No statement of auth is weakened by the port (ARCHITECTURE section 9, equivalence 4): each node's claim as
today's library stated it (`reference/auth`, put in namespace `Old` over the port's types) is equivalent to the
port's. Today's session table is a function from a token to the user it was issued to; the port's is the table
itself, a list of sessions each token issued once (`tokensIssuedOnce`), read as today's function by the user of the
session under the token (`asFunction`), which is the token's holder (`holderOf`). Today's definitions of the purpose's words are the port's claims of one
equation, each equivalent to the word being today's define. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Port
open Auth

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

/-- The token's holder is today's function at the token. -/
theorem holderOf_eq (s : Sessions) (t : String) : holderOf s t = asFunction s t := by
  unfold holderOf asFunction
  cases List.find? (fun x => decide (x.token = t)) s.open <;> rfl

/-- The token's holder has a grant for the path exactly when today's function gives a user at the token with one. -/
theorem holderGranted_iff (s : Sessions) (grants : List Grant) (t : String) (p : Path) :
    holderGranted s grants t p ↔ ∃ u, asFunction s t = some u ∧ Grant.mk u p ∈ grants := by
  simp only [holderGranted, holderOf_eq, grantFor_iff]

theorem accessExactly (access signedIn authorized) :
    Old.AccessExactly.claim UserId Path access signedIn authorized ↔
      Auth.accessExactly.claim access signedIn authorized := Iff.rfl

theorem accessNeedsGrant (admit grants) :
    Old.AccessNeedsGrant.claim admit grants ↔ Auth.accessNeedsGrant.claim admit grants := by
  simp only [Old.AccessNeedsGrant.claim, Auth.accessNeedsGrant.claim, grantFor_iff]

theorem tokenNamesHolder (admit) (s : Sessions) (hs : tokensIssuedOnce s) :
    Old.TokenNamesHolder.claim admit (asFunction s) ↔ Auth.tokenNamesHolder.claim admit s := by
  simp only [Old.TokenNamesHolder.claim, Auth.tokenNamesHolder.claim, issuedTo, asFunction]
  constructor
  · intro h _ t p u ha
    exact (asFunction_some _ hs t u).1 (h t p u ha)
  · intro h t p u ha
    exact (asFunction_some _ hs t u).2 (h hs t p u ha)

theorem grantLetsIn (admit grants) (s : Sessions) (hs : tokensIssuedOnce s) :
    Old.GrantLetsIn.claim (asFunction s) grants admit ↔ Auth.grantLetsIn.claim admit s grants := by
  simp only [Old.GrantLetsIn.claim, Auth.grantLetsIn.claim, holderGranted_iff, holderOf_eq]
  constructor
  · rintro h _ t p ⟨u, hu, hg⟩
    rw [hu]
    exact h t p u hu hg
  · intro h t p u hu hg
    rw [← hu]
    exact h hs t p ⟨u, hu, hg⟩

theorem decisionContract (admit grants) (s : Sessions) (hs : tokensIssuedOnce s) :
    Old.DecisionContract.claim (asFunction s) grants admit ↔ Auth.decisionContract.claim admit s grants := by
  unfold Old.DecisionContract.claim Old.DecisionContract.post Auth.decisionContract.claim
  constructor
  · intro h _ t p
    obtain ⟨h1, h2⟩ := h t p
    by_cases hg : holderGranted s grants t p
    · rw [ite_eq_left hg]
      obtain ⟨u, hu, hgu⟩ := (holderGranted_iff s grants t p).1 hg
      rw [holderOf_eq, hu]
      exact h2 u hu hgu
    · rw [ite_eq_right hg]
      cases ha : admit t p with
      | none => rfl
      | some u =>
        obtain ⟨hu, hgu⟩ := h1 u ha
        exact absurd ((holderGranted_iff s grants t p).2 ⟨u, hu, hgu⟩) hg
  · intro h t p
    have e := h hs t p
    refine ⟨fun u hu => ?_, fun u hu hg => ?_⟩
    · rw [e] at hu
      split at hu
      · rename_i hg
        obtain ⟨v, hv, hgv⟩ := (holderGranted_iff s grants t p).1 hg
        rw [holderOf_eq, hv] at hu
        cases hu
        exact ⟨hv, hgv⟩
      · cases hu
    · rw [e, ite_eq_left ((holderGranted_iff s grants t p).2 ⟨u, hu, hg⟩), holderOf_eq, hu]

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
  simp only [Auth.requests.claim, Old.access, admittedTo, Classical.not_forall, Classical.not_not]

end Port
