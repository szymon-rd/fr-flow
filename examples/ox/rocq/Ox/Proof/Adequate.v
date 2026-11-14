(** From a proof of a program that uses Ox to its runs.

    `scopes_adequacy`: a program started in one thread, proven in the logic from the invariant of scopes and
    the first thread's place (no fork, no scope open). In every state its threads reach, by any order of their
    steps, nothing has gone wrong, and there are steps of the system of scopes, each of which could be taken
    when it was, that the threads' places and the herds' sets agree with (`scopes_hold`).

    `scopes_laws`: so the roots of the model hold of those steps. The two leaves the roots are proven from
    (`startsSound`, `everyStepCanBeTaken`) are what the invariant keeps; the roots follow by the proofs FrFlow
    checks (`Proofs/OxScopes`). *)

From iris.algebra Require Import gmap.
From iris.base_logic.lib Require Import ghost_map mono_list invariants.
From iris.proofmode Require Import proofmode.
From Ox.Proof Require Export Ghost.
Require Import Proofs.OxScopes.noForkActsAfterItsScopeIsLeft Proofs.OxScopes.noForkIsMadeAfterItsScopeIsLeft
  Proofs.OxScopes.scopesAreLeftInsideOut.

(** What holds of a state: steps that could each be taken, places that agree with them, and each scope's set
    in the state with every fork of the scope that is not past its body. *)
Definition scopes_hold (σ : Machine.state code obj) : Prop :=
  ∃ taken places (herds : gset nat), agrees taken places herds ∧
    ∀ q, q ∈ herds → ∃ held : list val, s_ext σ q = Some (Held concurrent_set held) ∧ set_ok taken q held.

Lemma scopes_alloc `{!jvmGS code obj Σ, !scopesGpreS Σ} E (t : nat) :
  Wp.made t ={E}=∗ ∃ _ : scopesGS Σ, scopes_inv ∗ place_is t (Root, []).
Proof.
  iIntros "Hmade".
  iMod (mono_list_own_alloc ([] : list Step)) as (γt) "[Ht _]".
  iMod (ghost_map_alloc ({[t := (Root, [])]} : gmap nat place)) as (γp) "[Hp Hpl]".
  iMod (ghost_map_alloc_empty (K:=nat) (V:=unit)) as (γh) "Hh".
  set (G := ScopesGS Σ _ _ _ γp γh γt).
  iMod (inv_alloc scopesN E (scopes_body (scopesGS0 := G)) with "[-Hpl]") as "#Hinv".
  { iNext. iExists [], _, ∅. iFrame "Ht Hp Hh". iSplit; [iPureIntro; rewrite dom_empty_L; apply agrees_start |].
    iSplitL; [by rewrite dom_singleton_L big_sepS_singleton | by rewrite /sets big_sepM_empty]. }
  iModIntro. iExists G. iFrame "Hinv". by rewrite big_sepM_singleton.
Qed.

Lemma scopes_final `{!jvmGS code obj Σ, !scopesGS Σ} σ : scopes_inv -∗ jvm_interp σ ={⊤,∅}=∗ ⌜scopes_hold σ⌝.
Proof.
  iIntros "#Hinv Hσ". iInv "Hinv" as ">H" "_".
  iDestruct "H" as (taken places herds) "(%Ha & _ & _ & _ & _ & Hsets)".
  iAssert (∀ q, ⌜q ∈ dom herds⌝ →
    ⌜∃ held : list val, s_ext σ q = Some (Held concurrent_set held) ∧ set_ok taken q held⌝)%I as %Hsets.
  { iIntros (q [[] Hq]%elem_of_dom).
    iDestruct (big_sepM_lookup with "Hsets") as (held) "[Hext [%Hs _]]"; [exact Hq |].
    iDestruct (interp_ext with "Hσ Hext") as %He. iPureIntro. by exists held. }
  iApply fupd_mask_intro_discard; [set_solver |]. iPureIntro. by exists taken, places, (dom herds).
Qed.

Definition oxΣ : gFunctors := #[jvmΣ code obj; scopesΣ].

Section adequate.
  Context (interp : code → val → Machine.P code obj (Machine.res code obj)).
  Local Instance adequate_irisGS `{!jvmGS code obj Σ} : irisGS (jvm interp) Σ := jvm_irisGS interp.

  Theorem scopes_adequacy (t : tid) (c : code) (p : Machine.P code obj (Machine.res code obj))
      (σ0 : Machine.state code obj) (objects : gmap nat (Machine.object code obj)) :
    (∀ r, objects !! r = s_obj σ0 r) →
    (∀ r, s_ext σ0 r = None) →
    (∀ u, s_th σ0 u = if Nat.eqb u t then Some (Thread c TStarted false) else None) →
    s_wrong σ0 = None →
    (∀ `{!jvmGS code obj oxΣ, !scopesGS oxΣ},
       ⊢ scopes_inv -∗ place_is t (Root, []) -∗ ([∗ map] r ↦ o ∈ objects, r ↦obj o) -∗
         thread_is t c TStarted -∗ started t -∗
         WP (Running t p : running code obj) @ MaybeStuck; ⊤ {{ _, True }}) →
    ∀ pool σ, Machine.reaches interp ([Running t p], σ0) (pool, σ) → s_wrong σ = None ∧ scopes_hold σ.
  Proof.
    intros Hobj Hext Hth Hwrong Hwp.
    apply (jvm_adequacy interp oxΣ t c p σ0 objects scopes_hold Hobj Hext Hth Hwrong).
    iIntros (G) "Hobjs Hth #Hstarted Hmade".
    iMod (scopes_alloc ⊤ t with "Hmade") as (S) "[#Hinv Hplace]".
    iModIntro. iSplitL; [iApply (Hwp G S with "Hinv Hplace Hobjs Hth Hstarted") |].
    iIntros (σ) "Hσ". iApply (scopes_final with "Hinv Hσ").
  Qed.
End adequate.

(** The model's leaves, and so its roots, of the steps a state's places agree with. *)
Theorem scopes_laws σ : scopes_hold σ → ∃ taken,
    startsSound_claim none ∧ everyStepCanBeTaken_claim none taken ∧
    noForkActsAfterItsScopeIsLeft_claim taken ∧ noForkIsMadeAfterItsScopeIsLeft_claim taken ∧
    scopesAreLeftInsideOut_claim none taken.
Proof.
  intros (taken & places & herds & Ha & _). exists taken.
  pose proof none_is_sound as Hs. pose proof (a_valid _ _ _ Ha) as Hv.
  split; [exact Hs |]. split; [exact Hv |]. split; [| split].
  - exact (noForkActsAfterItsScopeIsLeft_Proofs_complete taken none Hs Hv).
  - exact (noForkIsMadeAfterItsScopeIsLeft_Proofs_complete taken none Hs Hv).
  - exact (scopesAreLeftInsideOut_Proofs_complete none taken Hs Hv).
Qed.
