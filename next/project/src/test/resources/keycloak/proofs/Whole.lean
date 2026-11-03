import FrFlowGen.Keycloak.Whole.Spec
import Proofs.Keycloak.Lemmas

/-! What is assumed of the server's store and of the requests it is handed, and what its programs are claimed to do,
hold together (owner §39): a store that keeps what it is given and logs the request (today's `storedAs`), an index
answering from the sessions the store holds (today's `storedSession`, `Lemmas.some_index`), changing nothing;
requests handed on that carry no token (a sign-out, fresh against every log); and what applications accept, what the
introspection answers. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.Whole.Proofs
open Keycloak

theorem consistent_3 : Obl.consistent_3 := by
  obtain ⟨lookup, hS, hLk⟩ := Lemmas.some_index
  let handed : StateM (List AuthRequest) AuthRequest := fun inbox => (AuthRequest.SignOut (RealmId.mk "") "", inbox)
  let storing : AuthRequest → ServerState → StateM Stored ServerState :=
    fun q after s => (after, Stored.mk s.loaded after (s.log ++ [q]))
  have hD : drawnTokens.claim handed := by
    intro w _ _ _
    rw [Lemmas.next_run_eq]
    intro t ht
    simp [handed, FrFlow.runOn, StateT.run, Id.run, tokenOf] at ht
  have hK : storeKeepsState.claim storing := fun q a w => rfl
  have hL : storeLogs.claim storing := fun q a w _ _ _ => rfl
  exact ⟨handed, storing, fun r t w => claimsOf (introspecting_run lookup r t w).1, lookup, hD, hK, hL,
    Lemmas.reference (introspecting_run lookup), Lemmas.introspect_answers lookup hS hLk, hS, hLk,
    Lemmas.loaded_kept handed storing lookup hD hK hL hLk, Lemmas.answers_stored handed storing hD hK hL⟩

end Keycloak.Whole.Proofs
