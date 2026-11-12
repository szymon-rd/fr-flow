(** Ox's scopes, as a caller uses them: what each needs and gives, proven of the code. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Code Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps Ox.Inner Ox.HerdProofs
  Ox.ScopeProofs.
Import ListNotations.
Open Scope list_scope.

(** ** `OxError.apply`: a capability is made, its herd opened *)

Definition opened (t : tid) (Γ0 Γ1 : gh) (cap : OxError) : Prop :=
  pushed t Γ0 Γ1 (OxError_herd cap) /\ g_fin Γ1 (OxError_finalizers cap) = true.

Lemma OxError_apply_spec t s em parent locals Γ0 (Q : exn + OxError -> gh -> Prop) :
  g_removed Γ0 t = false ->
  (forall cap Γ1, opened t Γ0 Γ1 cap -> Q (inr cap) Γ1) ->
  wp t (OxError_apply s em parent locals) Γ0 Q.
Proof.
  intros Hrm HQ. unfold OxError_apply.
  apply wp_bind. apply ThreadHerd_new_spec; [exact Hrm |].
  intros th Γ1 (HE1 & Hrm1 & Hop1 & Hwf1 & Hown1). cbn beta iota.
  apply wp_bind. apply wp_op. intros σ2 Γ2 HI2 HR2 Hs2.
  assert (Hrm2 : g_removed Γ2 t = false) by (rewrite (r_removed HR2); exact Hrm1).
  split; [exact Hrm2 |].
  intros x σ2' Hstep. cbn in Hstep. destruct Hstep as (r & Hnone & -> & ->).
  exists (set_fin Γ2 r). split; [apply inv_arnew; exact HI2 |]. split; [apply guar_arnew |].
  split; [intros u c _ Hst; exfalso; eapply no_starts_th; [| exact Hst]; reflexivity |].
  apply wp_ret. apply HQ.
  assert (HE2 : Ext Γ1 (set_fin Γ2 r)) by exact (Ext_trans (Rely_Ext HR2) (ext_set_fin Γ2 r)).
  split; [| cbn; apply upd_eq].
  cbn. split; [exact (Ext_trans HE1 HE2) |]. split; [exact Hrm2 |].
  split; [unfold set_fin; cbn; rewrite (r_open HR2); exact Hop1 |].
  split; [exact (wf_herd_Ext HE2 Hwf1) | exact Hown1].
Qed.

(** ** `runFinalizers`, for a scope no finalizer was registered on *)

Lemma runFinalizers_spec t scope result Γ0 (Q : res -> gh -> Prop) (Pst : gh -> Prop) :
  stable t Pst -> (forall Γ, Pst Γ -> g_removed Γ t = false) ->
  (forall Γ, Pst Γ -> g_fin Γ (OxError_finalizers scope) = true) ->
  Pst Γ0 -> (forall r Γ1, Pst Γ1 -> Q r Γ1) ->
  wp t (runFinalizers scope result) Γ0 Q.
Proof.
  intros Hst Hact Hfin HP HQ. unfold runFinalizers. cbn zeta.
  apply wp_bind. apply wp_op. intros σ Γ HI HR Hs.
  assert (HPΓ : Pst Γ) by (eapply Hst; eauto).
  split; [exact (Hact _ HPΓ) |].
  intros x σ' Hstep. cbn in Hstep. destruct Hstep as (v0 & Hv0 & -> & ->).
  exists Γ. split; [apply inv_artake; [exact HI | exact (Hfin _ HPΓ)] |].
  split; [intros u _; apply Rely_refl |].
  split; [intros u c _ Hstt; exfalso; eapply no_starts_th; [| exact Hstt]; reflexivity |].
  destruct (i_fin HI (Hfin _ HPΓ)) as [E | E]; rewrite Hv0 in E; injection E as ->.
  - cbn. apply HQ. exact HPΓ.
  - destruct result as [e | v]; cbn; apply HQ; exact HPΓ.
Qed.

(** ** `scopedWithCapability`: the body runs, the herd is closed, in every outcome *)

Lemma scopedWithCapability_spec t cap f rest Γ0 (Q : res -> gh -> Prop) :
  g_removed Γ0 t = false -> g_open Γ0 t = hid cap :: rest ->
  ThreadHerd_herdOwner (OxError_herd cap) = t -> g_fin Γ0 (OxError_finalizers cap) = true ->
  CallPre t f (VObj (O_OxError cap)) Γ0 ->
  (forall r Γ1, popped t Γ0 Γ1 rest -> Q r Γ1) ->
  wp t (scopedWithCapability cap f) Γ0 Q.
Proof.
  intros Hrm Hop Hown Hfin Hpre HQ. unfold scopedWithCapability. cbn zeta.
  (* what holds once the herd is closed *)
  pose (Pop := fun Γ => popped t Γ0 Γ rest /\ g_fin Γ (OxError_finalizers cap) = true).
  assert (HPst : stable t Pop).
  { intros Γ Γ' ((HE & Hr & Ho) & Hf) HR. split; [split; [exact (Ext_trans HE (Rely_Ext HR)) |] |].
    - split; [rewrite (r_removed HR); exact Hr | rewrite (r_open HR); exact Ho].
    - exact (r_fin HR Hf). }
  assert (HPact : forall Γ, Pop Γ -> g_removed Γ t = false) by (intros Γ ((_ & Hr & _) & _); exact Hr).
  (* the previous scope is read *)
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (-> & _). cbn beta iota.
  set (prev := j_tl σ1 currentScope t). clearbody prev.
  (* what follows the closing: the finalizers, then the previous scope is put back *)
  assert (Htail : forall result Γ, Pop Γ ->
    wp t (runFinalizers cap result) Γ (fun r Γ' =>
      wp t (call (TlSet currentScope prev)) Γ' (fun r2 Γ'' =>
        match r2 with inl e => Q (inl e) Γ'' | inr _ => Q r Γ'' end))).
  { intros result Γ HPΓ. apply (runFinalizers_spec t cap result Γ _ Pop HPst HPact); [| exact HPΓ |].
    - intros Γ' (_ & Hf). exact Hf.
    - intros r Γ' HP'. apply wp_frame; [exact I | apply can_step_intro; auto |].
      intros x Γ'' HR''. assert (HP'' : Pop Γ'') by (eapply HPst; eauto).
      destruct x; apply HQ; exact (proj1 HP''). }
  apply wp_try_finally.
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; rewrite (r_removed HR1); exact Hrm |].
  intros σ2 Γ2 x2 σ2' HI2 HR2 Hs2 Hstep2. cbn in Hstep2. destruct Hstep2 as (-> & _). cbn beta iota.
  assert (HK2 : Keep t Γ0 Γ2) by exact (Keep_Rely (Rely_Keep HR1) HR2).
  apply wp_bind. apply wp_try_catch. apply wp_bind. apply wp_try_finally.
  apply wp_invoke.
  - apply can_step_intro. rewrite (k_removed HK2). exact Hrm.
  - exact (CallPre_Keep HK2 Hpre).
  - intros r3 Γ3 HK3. assert (HK03 : Keep t Γ0 Γ3) by exact (Keep_trans HK2 HK3).
    apply (interruptAll_spec t (OxError_herd cap) rest).
    + rewrite (k_removed HK03). exact Hrm.
    + rewrite (k_open HK03). exact Hop.
    + exact Hown.
    + intros r4 Γ4 (HE4 & Hrm4 & Hop4).
      assert (HP4 : Pop Γ4).
      { split; [split; [exact (Ext_trans (k_ext HK03) HE4) | split; assumption] |].
        exact (e_fin (Ext_trans (k_ext HK03) HE4) Hfin). }
      destruct r4 as [e4 | []]; [| destruct r3 as [e3 | x3]]; cbn beta iota.
      * apply wp_ret. cbn beta iota. apply Htail. exact HP4.
      * apply wp_ret. cbn beta iota. apply Htail. exact HP4.
      * apply wp_ret. cbn beta iota. apply Htail. exact HP4.
Qed.
