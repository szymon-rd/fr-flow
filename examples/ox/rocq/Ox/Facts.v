(** Being inside a herd, and what the invariant gives of it. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

(** `h'` is `h` or one of the herds `h` was opened inside. *)
Inductive anc (Γ : gh) : nat -> nat -> Prop :=
  | anc_refl h : anc Γ h h
  | anc_step h hr h1 h2 : g_herd Γ h = Some hr -> h_parent hr = Some h1 -> anc Γ h1 h2 -> anc Γ h h2.

(** `u` is a fork of `h` that has not taken itself out, or owns `h` open. *)
Definition base (Γ : gh) (u : tid) (h : nat) : Prop :=
  ((exists b, g_role Γ u = ForkOf h b) /\ g_removed Γ u = false) \/ In h (g_open Γ u).

Definition inside (Γ : gh) (u : tid) (h : nat) : Prop := exists h0, base Γ u h0 /\ anc Γ h0 h.

Definition open_herd (Γ : gh) (h : nat) : Prop := exists hr, g_herd Γ h = Some hr /\ h_exited hr = false.

(** What every step keeps of the ghost state, whoever takes it. *)
Record Ext (Γ Γ' : gh) : Prop := {
  e_herd : forall h hr, g_herd Γ h = Some hr -> exists hr', g_herd Γ' h = Some hr' /\
      h_owner hr' = h_owner hr /\ h_parent hr' = h_parent hr /\ h_stamp hr' = h_stamp hr /\
      (h_exited hr = true -> h_exited hr' = true);
  e_fork : forall u h b, g_role Γ u = ForkOf h b -> g_role Γ' u = ForkOf h b;
  e_main : forall u, g_role Γ u = Main -> g_role Γ' u = Main;
  e_fin : forall r, g_fin Γ r = true -> g_fin Γ' r = true }.

Arguments e_herd {Γ Γ'} _ {h hr} _.
Arguments e_fork {Γ Γ'} _ {u h b} _.
Arguments e_main {Γ Γ'} _ {u} _.
Arguments e_fin {Γ Γ'} _ {r} _.

Lemma Rely_Ext t Γ Γ' : Rely t Γ Γ' -> Ext Γ Γ'.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7]. constructor; auto.
  intros h hr H. destruct (A1 _ _ H) as (hr' & ? & ? & ? & ? & ? & ?). exists hr'. auto.
Qed.

Lemma Ext_refl Γ : Ext Γ Γ.
Proof. constructor; intros; eauto 10. Qed.

Lemma Ext_trans Γ1 Γ2 Γ3 : Ext Γ1 Γ2 -> Ext Γ2 Γ3 -> Ext Γ1 Γ3.
Proof.
  intros [A1 A2 A3 A4] [B1 B2 B3 B4]. constructor; auto.
  intros h hr H. destruct (A1 _ _ H) as (hr' & E' & O' & P' & S' & X').
  destruct (B1 _ _ E') as (hr'' & E'' & O'' & P'' & S'' & X'').
  exists hr''. repeat split; try congruence; auto.
Qed.

Lemma anc_Ext Γ Γ' h h' : Ext Γ Γ' -> anc Γ h h' -> anc Γ' h h'.
Proof.
  intros HE Ha. induction Ha as [h | h hr h1 h2 Hh Hp _ IH]; [constructor |].
  destruct (e_herd HE Hh) as (hr' & Hh' & _ & Hp' & _). eapply anc_step; eauto. congruence.
Qed.

Lemma anc_trans Γ a b c : anc Γ a b -> anc Γ b c -> anc Γ a c.
Proof. intros H1 H2. induction H1; trivial. eapply anc_step; eauto. Qed.

(** What a thread knows of itself stays, whatever the others do. *)
Lemma base_Rely t Γ Γ' h : Rely t Γ Γ' -> base Γ t h -> base Γ' t h.
Proof.
  intros HR [((b & Hb) & Hrm) | Hin].
  - left. split; [exists b; eapply r_fork; eauto | rewrite (r_removed HR); trivial].
  - right. rewrite (r_open HR). trivial.
Qed.

Lemma inside_Rely t Γ Γ' h : Rely t Γ Γ' -> inside Γ t h -> inside Γ' t h.
Proof.
  intros HR (h0 & Hb & Ha). exists h0. split; [eapply base_Rely; eauto |].
  eapply anc_Ext; [eapply Rely_Ext; eauto | trivial].
Qed.

Lemma inside_anc Γ u h h' : inside Γ u h -> anc Γ h h' -> inside Γ u h'.
Proof. intros (h0 & Hb & Ha) Ha'. exists h0. split; trivial. eapply anc_trans; eauto. Qed.

Section WithInv.

  Variables (σ : jst) (Γ : gh).
  Hypothesis HI : Inv σ Γ.

  Lemma member_open u h b : g_role Γ u = ForkOf h b -> g_removed Γ u = false -> open_herd Γ h.
  Proof.
    intros Hr Hrm. destruct (i_fork HI Hr) as (Hreg & _).
    destruct (g_herd Γ h) as [hr |] eqn:E; [| contradiction].
    exists hr. split; trivial. destruct (h_exited hr) eqn:Ex; trivial.
    rewrite (i_exit HI E Ex Hr) in Hrm. discriminate.
  Qed.

  Lemma base_open u h : base Γ u h -> open_herd Γ h.
  Proof.
    intros [((b & Hb) & Hrm) | Hin].
    - eapply member_open; eauto.
    - apply (i_open HI _ _) in Hin. destruct Hin as (hr & ? & ? & ?). exists hr. auto.
  Qed.

  (** An open herd was opened inside an open herd. *)
  Lemma parent_open h hr h1 : g_herd Γ h = Some hr -> h_exited hr = false -> h_parent hr = Some h1 ->
    open_herd Γ h1.
  Proof.
    intros Hh Hex Hp.
    assert (Hin : In h (g_open Γ (h_owner hr))) by (apply (i_open HI _ _); exists hr; auto).
    destruct (in_split _ _ Hin) as (pre & post & Hsplit).
    pose proof (i_stack HI Hsplit Hh) as Hpar. rewrite Hp in Hpar.
    destruct post as [| h1' post'].
    - destruct (g_role Γ (h_owner hr)) eqn:Er; cbn in Hpar; try discriminate.
      injection Hpar as <-. eapply member_open; eauto.
      destruct (g_removed Γ (h_owner hr)) eqn:Erm; trivial.
      destruct (i_removed HI Erm) as (Hnil & _). rewrite Hnil in Hin. contradiction.
    - injection Hpar as <-.
      assert (Hin1 : In h1 (g_open Γ (h_owner hr))).
      { rewrite Hsplit. apply in_or_app. right. right. left. reflexivity. }
      apply (i_open HI _ _) in Hin1. destruct Hin1 as (hr1 & ? & ? & ?). exists hr1. auto.
  Qed.

  Lemma anc_open h h' : anc Γ h h' -> open_herd Γ h -> open_herd Γ h'.
  Proof.
    intros Ha. induction Ha as [h | h hr h1 h2 Hh Hp _ IH]; trivial.
    intros (hr0 & Hh0 & Hex). rewrite Hh in Hh0. injection Hh0 as <-.
    apply IH. eapply parent_open; eauto.
  Qed.

  (** A herd with a thread inside it is not exited. *)
  Theorem inside_open u h : inside Γ u h -> open_herd Γ h.
  Proof. intros (h0 & Hb & Ha). eapply anc_open; eauto. apply base_open with u. trivial. Qed.

End WithInv.

Arguments member_open {σ Γ} HI {u h b} _ _.
Arguments base_open {σ Γ} HI {u h} _.
Arguments parent_open {σ Γ} HI {h hr h1} _ _ _.
Arguments anc_open {σ Γ} HI {h h'} _ _.
Arguments inside_open {σ Γ} HI {u h} _.
