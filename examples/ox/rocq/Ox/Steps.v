(** Rules for single operations, and how the ghost updates sit with what a caller keeps. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates.
Import ListNotations.
Open Scope list_scope.

(** The rule for one operation, as `wp` states it. *)
Lemma wp_op {X} t (o : Jdk.op code obj (exn + X)) Γ0 (Q : exn + X -> gh -> Prop) :
  (forall σ Γ, Inv σ Γ -> Rely t Γ0 Γ -> started σ t -> Active t Γ /\
     forall x σ', opstep t o σ x σ' -> exists Γ', Inv σ' Γ' /\ Guar t Γ Γ' /\
       (forall u c, u <> t -> starts σ σ' u c -> StartPre u c Γ') /\ Q x Γ') ->
  wp t (call o) Γ0 Q.
Proof. intro H. exact H. Qed.

(** An operation that keeps the view, with its contract at hand for what it returned. *)
Lemma wp_frame_res {X} t (o : Jdk.op code obj (exn + X)) Γ0 (Q : exn + X -> gh -> Prop) :
  frame_op o -> can_step t Γ0 ->
  (forall σ Γ x σ', Inv σ Γ -> Rely t Γ0 Γ -> started σ t -> opstep t o σ x σ' -> Q x Γ) ->
  wp t (call o) Γ0 Q.
Proof.
  intros Hf Hc HQ. apply wp_op. intros σ Γ HI HR Hs. split; [eapply Hc; eauto |].
  intros x σ' Hstep. pose proof (opstep_frame Hf Hstep) as Hsv.
  exists Γ. split; [exact (inv_frame HI Hsv) |]. split; [intros u _; apply Rely_refl |].
  split; [| eapply HQ; eauto].
  intros u c _ Hst. exfalso. exact (sv_no_starts Hsv Hst).
Qed.

(** A program of such operations, between two things a thread knows. *)
Lemma wp_fo {A} t (m : P A) Γ (Q : A -> gh -> Prop) (Pst : gh -> Prop) :
  frameonly m -> stable t Pst -> (forall Γ1, Pst Γ1 -> g_removed Γ1 t = false) -> Pst Γ ->
  (forall x Γ1, Pst Γ1 -> Q x Γ1) -> wp t m Γ Q.
Proof.
  intros Hfo Hst Hact HP HQ. eapply wp_mono; [| exact (frameonly_wp t Pst Hfo Hst Hact Γ HP)].
  intros a Γ1 H1. cbn in H1. apply HQ, H1.
Qed.

(** A step that changes no thread starts none. *)
Lemma no_starts_th (σ σ' : jst) u c : j_th σ' = j_th σ -> ~ starts σ σ' u c.
Proof.
  intros E (Hn & Hs). apply Hn. unfold started. rewrite <- E.
  destruct (j_th σ' u) as [[c' s' i'] |]; [destruct s' |]; trivial.
Qed.

(** ** What a caller keeps across the ghost updates *)

Lemma Keep_Rely {t Γ1 Γ2 Γ3} : Keep t Γ1 Γ2 -> Rely t Γ2 Γ3 -> Keep t Γ1 Γ3.
Proof. intros H1 H2. eapply Keep_trans; [exact H1 | apply Rely_Keep, H2]. Qed.

Lemma ext_set_role Γ u r :
  (forall h b, g_role Γ u <> ForkOf h b) -> g_role Γ u <> Main -> Ext Γ (set_role Γ u r).
Proof.
  intros Hf Hm. constructor; cbn; trivial.
  - intros h hr H. exists hr. auto 10.
  - intros v h b Hr. rewrite upd_neq; [trivial | intros ->; exact (Hf _ _ Hr)].
  - intros v Hr. rewrite upd_neq; [trivial | intros ->; exact (Hm Hr)].
Qed.

Lemma keep_set_role t Γ u r :
  (forall h b, g_role Γ u <> ForkOf h b) -> g_role Γ u <> Main -> Keep t Γ (set_role Γ u r).
Proof. intros Hf Hm. constructor; cbn; trivial. apply ext_set_role; trivial. Qed.

Lemma ext_register Γ t h : g_herd Γ h = None -> Ext Γ (register Γ t h).
Proof.
  intro Hn. constructor; cbn; trivial.
  intros h' hr H. exists hr. rewrite upd_neq; [auto 10 | intros ->; congruence].
Qed.

Lemma ext_exit Γ t h hr rest : g_herd Γ h = Some hr -> Ext Γ (exit_herd Γ t h hr rest).
Proof.
  intro Hh. constructor; cbn; trivial.
  intros h' hr' H. destruct (Nat.eq_dec h' h) as [-> | Hne].
  - rewrite upd_eq. rewrite Hh in H. injection H as <-. eexists. split; [reflexivity |]. cbn. auto.
  - rewrite (upd_neq (g_herd Γ) h _ Hne). exists hr'. auto 10.
Qed.

Lemma ext_set_removed Γ u : Ext Γ (set_removed Γ u).
Proof. constructor; cbn; trivial. intros h hr H. exists hr. auto 10. Qed.

Lemma ext_set_fin Γ r : Ext Γ (set_fin Γ r).
Proof.
  constructor; cbn; trivial.
  - intros h hr H. exists hr. auto 10.
  - intros r' H. unfold upd. destruct (Nat.eq_dec r' r); trivial.
Qed.

(** ** What stays true along `Ext` and `Keep` *)

Lemma wf_herd_Ext {Γ Γ' th} : Ext Γ Γ' -> wf_herd Γ th -> wf_herd Γ' th.
Proof.
  intros HE (hr & Hh & Ho). destruct (e_herd HE Hh) as (hr' & Hh' & Ho' & _).
  exists hr'. split; [exact Hh' | congruence].
Qed.

Lemma wf_cap_Ext {Γ Γ' cap} : Ext Γ Γ' -> wf_cap Γ cap -> wf_cap Γ' cap.
Proof. intros HE (Hw & Hf). split; [exact (wf_herd_Ext HE Hw) | exact (e_fin HE Hf)]. Qed.

Lemma base_Keep {t Γ Γ' h} : Keep t Γ Γ' -> base Γ t h -> base Γ' t h.
Proof.
  intros HK [((b & Hb) & Hrm) | Hin].
  - left. split; [exists b; exact (e_fork (k_ext HK) Hb) | rewrite (k_removed HK); trivial].
  - right. rewrite (k_open HK). trivial.
Qed.

Lemma inside_Keep {t Γ Γ' h} : Keep t Γ Γ' -> inside Γ t h -> inside Γ' t h.
Proof.
  intros HK (h0 & Hb & Ha). exists h0. split; [exact (base_Keep HK Hb) |].
  exact (anc_Ext (k_ext HK) Ha).
Qed.

Lemma knows_Keep {t Γ Γ' cap} : Keep t Γ Γ' -> knows Γ t cap -> knows Γ' t cap.
Proof. intros HK (Hw & Hi). split; [exact (wf_cap_Ext (k_ext HK) Hw) | exact (inside_Keep HK Hi)]. Qed.
