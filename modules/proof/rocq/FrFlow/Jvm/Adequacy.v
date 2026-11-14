(** From a proof in the logic to every run of the machine.

    `jvm_adequacy`: a program started in one thread, over objects that are there from the start. If, given
    ownership of those objects and of the thread, the logic proves the thread (`WP`), then in every state the
    machine's threads reach, by any order of their steps, the state has not gone wrong: no thread ran a program
    with no meaning, called a method as its class is not known to have it, or read a field its object has not.
    And any fact that the logic's account of a state gives, with what the invariants hold, is true of every
    state reached (`φ`). *)

From iris.algebra Require Import gmap.
From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.
From FrFlow.Threads Require Import Prog.
From FrFlow.Jvm Require Export Rules.

Definition jvmΣ (code obj : Type) : gFunctors :=
  #[invΣ; ghost_mapΣ nat (Machine.object code obj); ghost_mapΣ nat (Machine.held code obj);
    ghost_mapΣ tid (code * tstatus); ghost_mapΣ tid unit].

Global Instance subG_jvmΣ {code obj Σ} : subG (jvmΣ code obj) Σ → jvmGpreS code obj Σ.
Proof. solve_inG. Qed.

Section adequacy.
  Context {code obj : Type}.
  Context (interp : code → Machine.val code obj → Machine.P code obj (Machine.res code obj)).

  Abbreviation mstate := (Machine.state code obj).
  Abbreviation thread := (running code obj).
  Local Instance adequacy_irisGS `{!jvmGS code obj Σ} : irisGS (jvm interp) Σ := jvm_irisGS interp.

  (** The machine's runs are the language's. *)
  Lemma reaches_rtc c c' : Machine.reaches interp c c' → rtc (@erased_step (jvm interp)) c c'.
  Proof.
    induction 1 as [| c c' c'' _ IH M]; [done |]. eapply rtc_r; [exact IH |].
    destruct M as [before e after σ e' σ' started Hstep]. exists [].
    by eapply (@step_atomic (jvm interp) _ _ _ e σ e' σ' started before after).
  Qed.

  Theorem jvm_adequacy Σ `{!jvmGpreS code obj Σ} (t : tid) (c : code) (p : Machine.P code obj (Machine.res code obj))
      (σ0 : mstate) (objects : gmap nat (Machine.object code obj)) (φ : mstate → Prop) :
    (∀ r, objects !! r = s_obj σ0 r) →
    (∀ r, s_ext σ0 r = None) →
    (∀ u, s_th σ0 u = if Nat.eqb u t then Some (Thread c TStarted false) else None) →
    s_wrong σ0 = None →
    (∀ `{!jvmGS code obj Σ},
       ⊢ ([∗ map] r ↦ o ∈ objects, r ↦obj o) -∗ thread_is t c TStarted -∗ started t -∗ made t ={⊤}=∗
         WP (Running t p : thread) @ MaybeStuck; ⊤ {{ _, True }} ∗
         (∀ σ, jvm_interp σ ={⊤,∅}=∗ ⌜φ σ⌝)) →
    ∀ pool σ, Machine.reaches interp ([Running t p], σ0) (pool, σ) → s_wrong σ = None ∧ φ σ.
  Proof.
    intros Hobj Hext Hth Hwrong Hwp pool σ Hreach%reaches_rtc.
    eapply (wp_invariance Σ (jvm interp) MaybeStuck (Running t p) σ0 pool σ); [| exact Hreach].
    iIntros (Hinv κs).
    iMod (ghost_map_alloc objects) as (γo) "[Ho Hobjs]".
    iMod (ghost_map_alloc (∅ : gmap nat (Machine.held code obj))) as (γe) "[He _]".
    iMod (ghost_map_alloc ({[t := (c, TStarted)]} : gmap tid (code * tstatus))) as (γt) "[Ht Hth]".
    iMod (ghost_map_alloc_empty (K:=tid) (V:=unit)) as (γs) "Hs".
    iMod (ghost_map_insert_persist t () with "Hs") as "[Hs #Hstarted]"; [done |].
    iMod (ghost_map_alloc_empty (K:=tid) (V:=unit)) as (γz) "Hz".
    iMod (ghost_map_alloc_empty (K:=tid) (V:=unit)) as (γn) "Hn".
    iMod (ghost_map_insert t () with "Hn") as "[Hn Hmade]"; [done |].
    set (G := JvmGS code obj Σ Hinv _ _ _ _ γo γe γt γs γz γn).
    iMod (Hwp G with "[Hobjs] [Hth] Hstarted Hmade") as "[Hwp Hφ]".
    { iApply (big_sepM_impl with "Hobjs"). by iIntros "!>" (r o _) "H". }
    { by rewrite big_sepM_singleton. }
    iModIntro. iExists (λ σ _ _, jvm_interp σ), (λ _, True%I).
    iSplitL "Ho He Ht Hs Hz Hn".
    - iExists objects, ∅, {[t := (c, TStarted)]}, {[t := ()]}, ∅, {[t := ()]}. iFrame. iSplit; [done |].
      iPureIntro. repeat split; try done.
      + intros u. rewrite Hth. destruct (Nat.eqb u t) eqn:E.
        * apply Nat.eqb_eq in E as ->. by rewrite lookup_singleton_eq.
        * apply Nat.eqb_neq in E. by rewrite lookup_singleton_ne.
      + intros u [[] Hu]. apply lookup_singleton_Some in Hu as [<- _]. unfold begun. by rewrite Hth Nat.eqb_refl.
      + by intros [? ?].
      + intros Ho. unfold over in Ho. rewrite Hth in Ho. by destruct (Nat.eqb u t).
      + intros u [[] Hu]. apply lookup_singleton_Some in Hu as [<- _]. by rewrite Hth Nat.eqb_refl.
    - iFrame "Hwp". iIntros "Hσ". iExists ∅.
      iDestruct (interp_right with "Hσ") as %Hw. iMod ("Hφ" with "Hσ") as %Hφ. by iPureIntro.
  Qed.

End adequacy.
