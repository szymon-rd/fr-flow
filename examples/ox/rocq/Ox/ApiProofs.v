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

(** ** `unsupervised` and `supervised`: a scope, as its caller sees it *)

(** What a caller owes to open a scope around a closure of its own: it has not ended, and it is inside the
    herd of every capability the closure holds. *)
Definition scope_pre (t : tid) (f : code) (Γ : gh) : Prop :=
  g_removed Γ t = false /\ is_client f /\ Forall (knows Γ t) (body_caps f).

Lemma scope_pre_Keep {t f Γ Γ'} : Keep t Γ Γ' -> scope_pre t f Γ -> scope_pre t f Γ'.
Proof.
  intros HK (Hrm & Hc & Hk). split; [rewrite (k_removed HK); exact Hrm |]. split; [exact Hc |].
  eapply Forall_impl; [| exact Hk]. intros cap H. exact (knows_Keep HK H).
Qed.

(** What a thread knew of a capability stays when it opens a herd. *)
Lemma knows_opened {t Γ Γ' cap c} : opened t Γ Γ' cap -> g_removed Γ t = false -> knows Γ t c -> knows Γ' t c.
Proof.
  intros ((HE & Hrm' & Hop' & _ & _) & _) Hrm (Hw & h0 & Hb & Ha).
  split; [exact (wf_cap_Ext HE Hw) |]. exists h0. split; [| exact (anc_Ext HE Ha)].
  destruct Hb as [((b & Hb) & _) | Hin].
  - left. split; [exists b; exact (e_fork HE Hb) | exact Hrm'].
  - right. rewrite Hop'. right. exact Hin.
Qed.

Lemma knows_new {t Γ Γ' cap} : opened t Γ Γ' cap -> knows Γ' t cap.
Proof.
  intros ((HE & Hrm' & Hop' & Hwf & _) & Hfin). split; [split; assumption |].
  exists (hid cap). split; [right; rewrite Hop'; left; reflexivity | constructor].
Qed.

Lemma closed_Keep {t Γ0 Γ2 Γ3 Γ4 cap} :
  Keep t Γ0 Γ2 -> opened t Γ2 Γ3 cap -> popped t Γ3 Γ4 (g_open Γ2 t) -> g_removed Γ0 t = false ->
  Keep t Γ0 Γ4.
Proof.
  intros HK ((HE3 & _) & _) (HE4 & Hrm4 & Hop4) Hrm.
  constructor; [exact (Ext_trans (k_ext HK) (Ext_trans HE3 HE4)) | congruence |].
  rewrite Hop4. exact (k_open HK).
Qed.

Lemma unsupervised_2_spec t locals f Γ0 (Q : res -> gh -> Prop) :
  scope_pre t f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (unsupervised_2 locals f) Γ0 Q.
Proof.
  intros Hpre HQ. unfold unsupervised_2. pose proof Hpre as (Hrm & Hc & Hk).
  pose (K := fun Γ => Keep t Γ0 Γ).
  assert (HKst : stable t K) by (intros Γ Γ' HK HR; exact (Keep_Rely HK HR)).
  assert (HKact : forall Γ, K Γ -> g_removed Γ t = false) by (intros Γ HK; rewrite (k_removed HK); exact Hrm).
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (-> & _). cbn beta iota.
  apply wp_bind. apply (wp_fo t _ Γ1 _ K); [apply fo_cast_option_OxError | exact HKst | exact HKact | exact (Rely_Keep HR1) |].
  intros [e | parent] Γ2 HK2; unfold K in HK2; [apply HQ; exact HK2 |].
  apply wp_bind. apply OxError_apply_spec; [exact (HKact _ HK2) |].
  intros cap Γ3 Hopen. pose proof Hopen as ((HE3 & Hrm3 & Hop3 & Hwf3 & Hown3) & Hfin3). cbn beta iota.
  apply (scopedWithCapability_spec t cap f (g_open Γ2 t)); trivial.
  - split; [destruct f; cbn in Hc; trivial; contradiction |]. split; [exact Hrm3 |].
    split; [| split].
    + apply Forall_app. split; [| cbn; constructor; [exact (knows_new Hopen) | constructor]].
      eapply Forall_impl; [| exact Hk]. intros c H.
      exact (knows_opened Hopen (HKact _ HK2) (knows_Keep HK2 H)).
    + intros cap' E. injection E as <-. unfold innermost. rewrite Hop3. reflexivity.
    + destruct f; cbn in Hc; trivial; contradiction.
  - intros r Γ4 Hpop. apply HQ. exact (closed_Keep HK2 Hopen Hpop Hrm).
Qed.

Lemma unsupervised_1_spec t f Γ0 (Q : res -> gh -> Prop) :
  scope_pre t f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (unsupervised_1 f) Γ0 Q.
Proof.
  intros Hpre HQ. unfold unsupervised_1. pose proof Hpre as (Hrm & _).
  pose (K := fun Γ => Keep t Γ0 Γ).
  apply wp_bind. apply (wp_fo t _ Γ0 _ K); [apply fo_currentLocals | | | apply Keep_refl |].
  { intros Γ Γ' HK HR. exact (Keep_Rely HK HR). }
  { intros Γ HK. rewrite (k_removed HK). exact Hrm. }
  intros [e | locals] Γ1 HK1; unfold K in HK1; [apply HQ; exact HK1 |].
  apply unsupervised_2_spec; [exact (scope_pre_Keep HK1 Hpre) |].
  intros r Γ2 HK2. apply HQ. exact (Keep_trans HK1 HK2).
Qed.

Lemma supervisedError_2_spec t em locals f Γ0 (Q : res -> gh -> Prop) :
  scope_pre t f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (supervisedError_2 em locals f) Γ0 Q.
Proof.
  intros Hpre HQ. unfold supervisedError_2. pose proof Hpre as (Hrm & Hc & Hk).
  pose (K := fun Γ => Keep t Γ0 Γ).
  assert (HKst : stable t K) by (intros Γ Γ' HK HR; exact (Keep_Rely HK HR)).
  assert (HKact : forall Γ, K Γ -> g_removed Γ t = false) by (intros Γ HK; rewrite (k_removed HK); exact Hrm).
  apply wp_bind. apply (wp_fo t _ Γ0 _ K); [apply fo_DefaultSupervisor_new | exact HKst | exact HKact | apply Keep_refl |].
  intros [e | s] Γa HKa; unfold K in HKa; [apply HQ; exact HKa |].
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact (HKact _ HKa) |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (-> & _). cbn beta iota.
  apply wp_bind. apply (wp_fo t _ Γ1 _ K); [apply fo_cast_option_OxError | exact HKst | exact HKact | exact (Keep_Rely HKa HR1) |].
  intros [e | parent] Γ2 HK2; unfold K in HK2; [apply HQ; exact HK2 |].
  apply wp_bind. apply OxError_apply_spec; [exact (HKact _ HK2) |].
  intros cap Γ3 Hopen. pose proof Hopen as ((HE3 & Hrm3 & Hop3 & Hwf3 & Hown3) & Hfin3). cbn beta iota.
  assert (Hinn : innermost Γ3 t (hid cap)) by (unfold innermost; rewrite Hop3; reflexivity).
  (* whatever the scope gives, what follows touches nothing the invariant reads *)
  assert (Hrest : forall Γ4, popped t Γ3 Γ4 (g_open Γ2 t) -> K Γ4).
  { intros Γ4 Hpop. exact (closed_Keep HK2 Hopen Hpop Hrm). }
  apply wp_try_catch. apply wp_bind.
  apply (scopedWithCapability_spec t cap (Lam_supervisedError_1 s em cap f) (g_open Γ2 t)); trivial.
  - split; [exact Hc |]. split; [exact Hrm3 |]. split; [| split; [| exact Hinn]].
    + cbn. constructor; [exact (knows_new Hopen) |].
      apply Forall_app. split; [| constructor; [exact (knows_new Hopen) | constructor]].
      eapply Forall_impl; [| exact Hk]. intros c H.
      exact (knows_opened Hopen (HKact _ HK2) (knows_Keep HK2 H)).
    + intros cap' E. injection E as <-. exact Hinn.
  - intros [e | scopeResult] Γ4 Hpop; pose proof (Hrest Γ4 Hpop) as HK4.
    + (* the scope threw: the handler *)
      apply (wp_fo t _ Γ4 _ K); [fo1 | exact HKst | exact HKact | exact HK4 |].
      intros x Γ5 HK5. apply HQ. exact HK5.
    + apply (wp_fo t _ Γ4 _ K); [fo1 | exact HKst | exact HKact | exact HK4 |].
      intros [e | v] Γ5 HK5; unfold K in HK5; [| apply HQ; exact HK5].
      (* what follows threw: the handler *)
      apply (wp_fo t _ Γ5 _ K); [fo1 | exact HKst | exact HKact | exact HK5 |].
      intros x Γ6 HK6. apply HQ. exact HK6.
Qed.

Lemma supervisedError_1_spec t em f Γ0 (Q : res -> gh -> Prop) :
  scope_pre t f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (supervisedError_1 em f) Γ0 Q.
Proof.
  intros Hpre HQ. unfold supervisedError_1. pose proof Hpre as (Hrm & _).
  pose (K := fun Γ => Keep t Γ0 Γ).
  apply wp_bind. apply (wp_fo t _ Γ0 _ K); [apply fo_currentLocals | | | apply Keep_refl |].
  { intros Γ Γ' HK HR. exact (Keep_Rely HK HR). }
  { intros Γ HK. rewrite (k_removed HK). exact Hrm. }
  intros [e | locals] Γ1 HK1; unfold K in HK1; [apply HQ; exact HK1 |].
  apply supervisedError_2_spec; [exact (scope_pre_Keep HK1 Hpre) |].
  intros r Γ2 HK2. apply HQ. exact (Keep_trans HK1 HK2).
Qed.

Theorem supervised_spec t f Γ0 (Q : res -> gh -> Prop) :
  scope_pre t f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (supervised f) Γ0 Q.
Proof. intros Hpre HQ. unfold supervised. apply supervisedError_1_spec; assumption. Qed.
