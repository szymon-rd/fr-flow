(** `ox.internal.ThreadHerd`, method by method: what each needs and gives, proven of the code. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Code Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps.
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
  callable b -> plain b ->
  Forall (fun cap => wf_cap Γ0 cap /\ anc Γ0 (ThreadHerd_threads th) (hid cap)) (body_caps b) ->
  (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) ->
  wp t (ThreadHerd_startThread th b) Γ0 Q.
Proof.
  intros Hrm Hin Hcal Hpl Hcaps HQ. unfold ThreadHerd_startThread.
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
      split; [exact Hpl |].
      eapply Forall_impl; [| exact Hcaps]. intros cap (Hw & Ha).
      split; [exact (wf_cap_Ext (k_ext HK7) Hw) | exact (anc_Ext (k_ext HK7) Ha)].
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
