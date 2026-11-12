(** `ox.internal.ThreadHerd`, method by method: what each needs and gives, proven of the code. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps Ox.Inner.
Import ListNotations.
Open Scope list_scope.

(** ** The constructor: a herd is opened, its owner the caller *)

Definition pushed (t : tid) (Γ0 Γ1 : gh) (th : ThreadHerd) : Prop :=
  Ext Γ0 Γ1 /\ g_removed Γ1 t = false /\ g_open Γ1 t = ThreadHerd_threads th :: g_open Γ0 t /\
  wf_herd Γ1 th /\ ThreadHerd_herdOwner th = t.

Lemma ThreadHerd_new_spec t tf Γ0 (Q : exn + ThreadHerd -> gh -> Prop) :
  g_removed Γ0 t = false ->
  (forall th Γ1, pushed t Γ0 Γ1 th -> Q (inr th) Γ1) ->
  wp t (ThreadHerd_new tf) Γ0 Q.
Proof.
  intros Hrm HQ. unfold ThreadHerd_new.
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm |].
  intros σ Γ x σ' HI HR Hs Hstep. cbn in Hstep. destruct Hstep as (-> & _).
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; rewrite (r_removed HR); exact Hrm |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (r & _ & -> & _).
  apply wp_bind. apply wp_op. intros σ2 Γ2 HI2 HR2 Hs2.
  assert (HR02 : Rely t Γ0 Γ2) by (eapply Rely_trans; [eapply Rely_trans |]; eauto).
  assert (Hrm2 : g_removed Γ2 t = false) by (rewrite (r_removed HR02); exact Hrm).
  split; [exact Hrm2 |].
  intros x2 σ2' Hstep2. cbn in Hstep2. destruct Hstep2 as (h & Hnone & -> & ->).
  exists (register Γ2 t h). split; [eapply inv_register; eauto |].
  split; [eapply guar_register; eauto |].
  split; [intros u c _ Hst; exfalso; eapply no_starts_th; [| exact Hst]; reflexivity |].
  apply wp_ret. apply HQ. unfold pushed. cbn. split; [| split; [| split; [| split]]].
  - eapply Ext_trans; [exact (Rely_Ext HR02) | apply ext_register; exact (unregistered HI2 Hnone)].
  - exact Hrm2.
  - rewrite upd_eq, (r_open HR02). reflexivity.
  - eexists. split; [apply upd_eq | reflexivity].
  - reflexivity.
Qed.

(** ** The checks: they touch nothing the invariant reads *)

Ltac fo :=
  repeat first
    [ apply fo_retM | apply fo_throw | apply fo_ret
    | apply fo_bind | apply fo_try_catch | apply fo_try_finally
    | apply fo_loop | apply fo_while | apply fo_TsForEach | apply fo_EsForEach | apply fo_VsForEach
    | apply fo_List_foreach | apply fo_extern | apply fo_type_error
    | (apply fo_call; exact I)
    | intro
    | match goal with |- frameonly (match ?x with _ => _ end) => destruct x end ].

Lemma fo_isOwnerOrHerdThread th u : frameonly (ThreadHerd_isOwnerOrHerdThread th u).
Proof. unfold ThreadHerd_isOwnerOrHerdThread. fo. Qed.

Lemma fo_assertNotShuttingDown th : frameonly (ThreadHerd_assertNotShuttingDown th).
Proof. unfold ThreadHerd_assertNotShuttingDown. fo. Qed.

Lemma fo_cast_OxError v : frameonly (cast_OxError v).
Proof. unfold cast_OxError. fo. Qed.

Lemma fo_verify th : frameonly (ThreadHerd_verifyCurrentThreadInScopeTree th).
Proof.
  unfold ThreadHerd_verifyCurrentThreadInScopeTree. fo.
  all: first [apply fo_isOwnerOrHerdThread | apply fo_cast_OxError].
Qed.

(** ** `startThread`: a fork is made, put in the set, started *)

Lemma ThreadHerd_startThread_spec t th b Γ0 (Q : exn + unit -> gh -> Prop) :
  g_removed Γ0 t = false ->
  inside Γ0 t (ThreadHerd_threads th) ->
  callable b -> plain b -> main_of (ThreadHerd_threads th) b ->
  Forall (reaches Γ0 t (ThreadHerd_threads th)) (body_caps b) ->
  (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) ->
  wp t (ThreadHerd_startThread th b) Γ0 Q.
Proof.
  intros Hrm Hin Hcal Hpl Hmain Hcaps HQ. unfold ThreadHerd_startThread.
  set (h := ThreadHerd_threads th) in *.
  pose (K := fun Γ => Keep t Γ0 Γ).
  assert (HKst : stable t K) by (intros Γ Γ' HK HR; exact (Keep_Rely HK HR)).
  assert (HKact : forall Γ, K Γ -> g_removed Γ t = false).
  { intros Γ HK. rewrite (k_removed HK). exact Hrm. }
  apply wp_bind. apply (wp_fo t _ Γ0 _ K); [apply fo_assertNotShuttingDown | exact HKst | exact HKact | apply Keep_refl |].
  intros [e | []] Γ1 HK1; [apply HQ; exact HK1 |].
  apply wp_bind. apply (wp_fo t _ Γ1 _ K); [apply fo_verify | exact HKst | exact HKact | exact HK1 |].
  intros [e | []] Γ2 HK2; [apply HQ; exact HK2 |].
  (* the thread is made *)
  apply wp_bind. apply wp_op. intros σ3 Γ3 HI3 HR3 Hs3.
  assert (HK3 : K Γ3) by (eapply HKst; eauto).
  split; [exact (HKact _ HK3) |].
  intros x σ3' Hstep. cbn in Hstep. destruct Hstep as (u & Hnone & -> & ->).
  pose proof (i_none HI3 Hnone) as Hrole.
  exists (set_role Γ3 u (Created t th b)).
  split; [apply inv_newthread; assumption |].
  split; [eapply guar_newthread; eauto |].
  split.
  { intros v c _ (Hn & Hst). exfalso. cbn in Hst. unfold upd in Hst.
    destruct (Nat.eq_dec v u); [exact Hst |]. apply Hn. unfold started.
    destruct (j_th σ3 v) as [[c' s' i'] |]; [destruct s' |]; trivial; contradiction. }
  assert (HK4 : Keep t Γ0 (set_role Γ3 u (Created t th b))).
  { eapply Keep_trans; [exact HK3 |]. apply keep_set_role; rewrite Hrole; [intros; discriminate | discriminate]. }
  (* it is put in the set *)
  pose (A := fun Γ => Keep t Γ0 Γ /\ g_role Γ u = Created t th b).
  apply wp_bind. apply wp_op. intros σ5 Γ5 HI5 HR5 Hs5.
  assert (HK5 : Keep t Γ0 Γ5) by exact (Keep_Rely HK4 HR5).
  assert (Hr5 : g_role Γ5 u = Created t th b).
  { apply (r_created HR5). cbn. apply upd_eq. }
  split; [exact (HKact _ HK5) |].
  intros x5 σ5' Hstep5. cbn in Hstep5. destruct Hstep5 as (s & Hs & -> & ->).
  assert (Hopen : open_herd Γ5 h) by (eapply inside_open; [exact HI5 | exact (inside_Keep HK5 Hin)]).
  exists (set_role Γ5 u (ForkOf h b)).
  split; [eapply inv_add; eauto |].
  split; [eapply guar_add; eauto |].
  split; [intros v c _ Hst; exfalso; eapply no_starts_th; [| exact Hst]; reflexivity |].
  assert (HK6 : Keep t Γ0 (set_role Γ5 u (ForkOf h b))).
  { eapply Keep_trans; [exact HK5 |]. apply keep_set_role; rewrite Hr5; [intros; discriminate | discriminate]. }
  (* it is started *)
  apply wp_op. intros σ7 Γ7 HI7 HR7 Hs7.
  assert (HK7 : Keep t Γ0 Γ7) by exact (Keep_Rely HK6 HR7).
  assert (Hr7 : g_role Γ7 u = ForkOf h b).
  { apply (r_fork HR7). cbn. apply upd_eq. }
  split; [exact (HKact _ HK7) |].
  intros x7 σ7' Hstep7. cbn in Hstep7.
  destruct (i_fork HI7 Hr7) as (Hreg & th' & st & i & Eu & Hth').
  rewrite Eu in Hstep7. exists Γ7. destruct st.
  - (* not started: it starts *)
    destruct Hstep7 as (-> & ->).
    split; [eapply inv_start; eauto |].
    split; [intros v _; apply Rely_refl |].
    split; [| apply HQ; exact HK7].
    intros v c Hv (Hn & Hst). cbn in Hst. unfold upd in Hst. destruct (Nat.eq_dec v u) as [-> | Hvu].
    + subst c. cbn. rewrite Hth'.
      assert (Hnb : ~ begun σ7 u) by (unfold begun; rewrite Eu; tauto).
      destruct (i_new HI7 Hnb) as (Hrmu & Hopu).
      split; [eauto |]. split; [exact Hrmu |]. split; [exact Hopu |]. split; [exact Hcal |].
      split; [exact Hpl |]. split; [exact Hmain |].
      eapply Forall_impl; [| exact Hcaps]. intros cap (Hw & Ha).
      split; [exact (wf_cap_Ext (k_ext HK7) Hw) |].
      destruct Ha as [Ha | (Hinn & Hins)]; [exact (anc_Ext (k_ext HK7) Ha) |].
      eapply inner_anc; [exact HI7 | exact (innermost_Keep HK7 Hinn) | exact (inside_Keep HK7 Hins)].
    + exfalso. apply Hn. unfold started.
      destruct (j_th σ7 v) as [[c' s' i'] |]; [destruct s' |]; trivial; contradiction.
  - destruct Hstep7 as (-> & ->).
    split; [exact HI7 |]. split; [intros v _; apply Rely_refl |].
    split; [| apply HQ; exact HK7].
    intros v c _ Hst. exfalso. eapply no_starts_th; [| exact Hst]. reflexivity.
  - destruct Hstep7 as (-> & ->).
    split; [exact HI7 |]. split; [intros v _; apply Rely_refl |].
    split; [| apply HQ; exact HK7].
    intros v c _ Hst. exfalso. eapply no_starts_th; [| exact Hst]. reflexivity.
Qed.

(** ** A fork's thread: it runs its body, then takes itself out of the set *)

Lemma runnable_spec u th b Γ0 :
  StartPre u (Lam_ThreadHerd_startThread_1 th b) Γ0 ->
  wp u (Lam_ThreadHerd_startThread_1_body th b VUnit) Γ0 (Done u).
Proof.
  intros ((b0 & Hrole) & Hrm & Hop & Hcal & Hpl & Hmain & Hcaps). unfold Lam_ThreadHerd_startThread_1_body.
  set (h := ThreadHerd_threads th) in *.
  assert (Hin : inside Γ0 u h).
  { exists h. split; [left; split; [eauto | exact Hrm] | constructor]. }
  apply wp_try_finally. apply wp_invoke.
  - apply can_step_intro. exact Hrm.
  - unfold CallPre. split; [exact Hcal |]. split; [exact Hrm |]. split; [| split].
    + rewrite app_nil_r. eapply Forall_impl; [| exact Hcaps]. intros cap (Hw & Ha).
      split; [exact Hw | exact (inside_anc Hin Ha)].
    + intros cap E. discriminate.
    + apply (main_of_extra (h := h)); trivial. unfold innermost. rewrite Hop. split; [eauto | exact Hrm].
  - intros r Γ1 HK1.
    assert (Hrm1 : g_removed Γ1 u = false) by (rewrite (k_removed HK1); exact Hrm).
    apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm1 |].
    intros σ2 Γ2 x σ2' HI2 HR2 Hs2 Hstep2. cbn in Hstep2. destruct Hstep2 as (-> & _).
    assert (HK2 : Keep u Γ0 Γ2) by exact (Keep_Rely HK1 HR2).
    apply wp_bind. apply wp_op. intros σ3 Γ3 HI3 HR3 Hs3.
    assert (HK3 : Keep u Γ0 Γ3) by exact (Keep_Rely HK2 HR3).
    assert (Hrm3 : g_removed Γ3 u = false) by (rewrite (k_removed HK3); exact Hrm).
    assert (Hop3 : g_open Γ3 u = []) by (rewrite (k_open HK3); exact Hop).
    pose proof (e_fork (k_ext HK3) Hrole) as Hrole3.
    split; [exact Hrm3 |].
    intros x3 σ3' Hstep3. cbn in Hstep3. destruct Hstep3 as (s & Hs & -> & ->).
    exists (set_removed Γ3 u).
    split; [eapply inv_remove; eauto |].
    split; [apply guar_remove |].
    split; [intros v c _ Hst; exfalso; eapply no_starts_th; [| exact Hst]; reflexivity |].
    apply wp_ret. destruct r; unfold Done; cbn; exact Hop3.
Qed.

(** ** The closing loop: when it finds the set empty, the herd is exited *)

Definition popped (t : tid) (Γ0 Γ1 : gh) (rest : list nat) : Prop :=
  Ext Γ0 Γ1 /\ g_removed Γ1 t = false /\ g_open Γ1 t = rest.

(** A program that throws nothing and keeps what its thread knew. *)
Definition quiet {X : Type} (A : gh -> Prop) : exn + X -> gh -> Prop :=
  fun r Γ => match r with inl _ => False | inr _ => A Γ end.

Lemma TsForEach_quiet {S} t r (f : tid -> S -> M S) (s : S) Γ (A : gh -> Prop) :
  stable t A -> (forall Γ1, A Γ1 -> g_removed Γ1 t = false) -> A Γ ->
  (forall u s1 Γ1, A Γ1 -> wp t (f u s1) Γ1 (quiet A)) ->
  wp t (TsForEach r f s) Γ (quiet A).
Proof.
  intros Hst Hact HA Hf. unfold TsForEach. apply wp_loop with (J := fun _ Γ1 => A Γ1); [exact HA |].
  intros [seen s1] Γ1 HA1. split; [apply can_step_intro; auto |].
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; auto |].
  intros σ Γ2 x σ' HI HR Hs Hstep. cbn in Hstep. destruct Hstep as (_ & _ & Hx).
  assert (HA2 : A Γ2) by (eapply Hst; eauto).
  destruct x as [e | [u |]]; [contradiction | |].
  - apply wp_bind. eapply wp_mono; [| apply Hf; exact HA2].
    intros [e | s2] Γ3 H3; cbn in H3; [contradiction |]. apply wp_ret. exact H3.
  - apply wp_ret. exact HA2.
Qed.

Lemma interruptAll_spec t th rest Γ0 (Q : exn + unit -> gh -> Prop) :
  g_removed Γ0 t = false -> g_open Γ0 t = ThreadHerd_threads th :: rest -> ThreadHerd_herdOwner th = t ->
  (forall r Γ1, popped t Γ0 Γ1 rest -> Q r Γ1) ->
  wp t (ThreadHerd_interruptAllAndJoinUntilCompleted th) Γ0 Q.
Proof.
  intros Hrm Hop Hown HQ. unfold ThreadHerd_interruptAllAndJoinUntilCompleted.
  set (h := ThreadHerd_threads th) in *.
  pose (A := fun Γ => Ext Γ0 Γ /\ g_removed Γ t = false /\ g_open Γ t = h :: rest).
  assert (HAst : stable t A).
  { intros Γ Γ' (HE & Hr & Ho) HR. split; [exact (Ext_trans HE (Rely_Ext HR)) |].
    split; [rewrite (r_removed HR); exact Hr | rewrite (r_open HR); exact Ho]. }
  assert (HAact : forall Γ, A Γ -> g_removed Γ t = false) by (intros Γ (_ & Hr & _); exact Hr).
  assert (HA0 : A Γ0) by (split; [apply Ext_refl | split; assumption]).
  (* the owner check passes *)
  apply wp_bind. unfold ThreadHerd_assertOnOwnerThread.
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (-> & _).
  rewrite Hown, Nat.eqb_refl. cbn [negb]. apply wp_ret. cbn beta iota.
  assert (HA1 : A Γ1) by (eapply HAst; eauto).
  (* the flag is set *)
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; auto |].
  intros σ2 Γ2 x2 σ2' HI2 HR2 Hs2 Hstep2. cbn in Hstep2. destruct Hstep2 as (_ & -> & _).
  assert (HA2 : A Γ2) by (eapply HAst; eauto).
  (* the loop *)
  cbn zeta. apply wp_bind. unfold while.
  apply wp_loop with (J := fun _ Γ => A Γ); [exact HA2 |].
  intros st Γ3 HA3. split; [apply can_step_intro; auto |].
  apply wp_bind. apply wp_bind. apply wp_op. intros σ4 Γ4 HI4 HR4 Hs4.
  assert (HA4 : A Γ4) by (eapply HAst; eauto). destruct HA4 as (HE4 & Hrm4 & Hop4).
  split; [exact Hrm4 |].
  intros x4 σ4' Hstep4. cbn in Hstep4. destruct Hstep4 as (s & Hs & -> & Hx).
  assert (Hin : In h (g_open Γ4 t)) by (rewrite Hop4; left; trivial).
  apply (i_open HI4) in Hin. destruct Hin as (hr & Hh & Hho & Hhx).
  destruct Hx as [(-> & Hempty) | (-> & Hsome)].
  - (* empty: the herd is exited, and the loop ends *)
    exists (exit_herd Γ4 t h hr rest).
    split; [eapply inv_exit; eauto |].
    split; [apply guar_exit; assumption |].
    split; [intros v c _ Hst; exfalso; eapply no_starts_th; [| exact Hst]; reflexivity |].
    apply wp_ret. cbn beta iota. cbn [negb]. apply wp_ret. cbn beta iota.
    assert (Hpop : popped t Γ0 (exit_herd Γ4 t h hr rest) rest).
    { split; [exact (Ext_trans HE4 (ext_exit Γ4 t h hr rest Hh)) |]. split; [exact Hrm4 |]. cbn. apply upd_eq. }
    destruct st as [its [e |]]; [apply wp_throw | apply wp_ret]; apply HQ; exact Hpop.
  - (* not empty: every thread in the set is interrupted and joined *)
    exists Γ4. split; [exact HI4 |]. split; [intros v _; apply Rely_refl |].
    split; [intros v c _ Hst; exfalso; eapply no_starts_th; [| exact Hst]; reflexivity |].
    apply wp_ret. cbn beta iota. cbn [negb]. apply wp_bind.
    assert (HA4 : A Γ4) by (split; [| split]; assumption).
    assert (Hint : forall its u Γ, A Γ ->
      wp t (if negb (tset_contains its u) then bind (call (ThreadInterrupt u)) (fun _ => ret (tset_add its u))
            else ret its) Γ (quiet A)).
    { intros its u Γ HAΓ. destruct (negb (tset_contains its u)).
      - apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; auto |].
        intros σ Γ' x σ' HI HR Hsx Hstep. cbn in Hstep. destruct Hstep as (-> & _).
        cbn beta iota. apply wp_ret. unfold quiet. eapply HAst; eauto.
      - apply wp_ret. exact HAΓ. }
    apply wp_mono with (Q := quiet A).
    { intros [e | s'] Γ5 H5; [exact (False_ind _ H5) | apply wp_ret; exact H5]. }
    destruct st as [its ie]. cbn beta iota. apply wp_bind. apply wp_mono with (Q := quiet A).
    2: { apply TsForEach_quiet; [exact HAst | exact HAact | exact HA4 |].
         intros u s1 Γ HAΓ. apply Hint. exact HAΓ. }
    intros [e | its'] Γ5 H5; [exact H5 |]. cbn beta iota.
    apply TsForEach_quiet; [exact HAst | exact HAact | exact H5 |].
    intros u [its1 ie1] Γ HAΓ. apply wp_bind. apply wp_mono with (Q := quiet A).
    2: { apply Hint. exact HAΓ. }
    intros [e | its2] Γ6 H6; [exact H6 |]. cbn beta iota.
    apply wp_bind. apply wp_try_catch. apply wp_bind.
    apply wp_frame_res; [exact I | apply can_step_intro; auto |].
    intros σ Γ7 x σ' HI HR Hsx Hstep. cbn in Hstep.
    assert (HA7 : A Γ7) by (eapply HAst; eauto).
    destruct Hstep as [(-> & _) | (-> & _)].
    + cbn beta iota. apply wp_ret. cbn beta iota. apply wp_ret. exact HA7.
    + cbn beta iota. destruct ie1 as [e1 |].
      * apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; auto |].
        intros σ8 Γ8 x8 σ8' HI8 HR8 Hs8 Hstep8. cbn in Hstep8. destruct Hstep8 as (-> & _).
        cbn beta iota. apply wp_ret. cbn beta iota. apply wp_ret. unfold quiet. eapply HAst; eauto.
      * apply wp_ret. cbn beta iota. apply wp_ret. exact HA7.
Qed.
