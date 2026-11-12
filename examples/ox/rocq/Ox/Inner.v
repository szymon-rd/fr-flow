(** The herd a thread is most deeply inside, and the order of herds by when they were opened. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps.
Import ListNotations.
Open Scope list_scope.

Lemma innermost_Keep {t Γ Γ' h} : Keep t Γ Γ' -> innermost Γ t h -> innermost Γ' t h.
Proof.
  intros HK. unfold innermost. rewrite (k_open HK). destruct (g_open Γ t); trivial.
  intros ((b & Hb) & Hrm). split; [exists b; exact (e_fork (k_ext HK) Hb) | rewrite (k_removed HK); exact Hrm].
Qed.

Lemma CallPre_Keep {t c arg Γ Γ'} : Keep t Γ Γ' -> CallPre t c arg Γ -> CallPre t c arg Γ'.
Proof.
  intros HK (Hc & Hrm & Hk & Ha & Hm). split; [exact Hc |].
  split; [rewrite (k_removed HK); exact Hrm |].
  split; [eapply Forall_impl; [| exact Hk]; intros cap H; exact (knows_Keep HK H) |].
  split; [intros cap E; exact (innermost_Keep HK (Ha cap E)) |].
  clear Hc Hk Ha. induction c; cbn in *; trivial; try (exact (innermost_Keep HK Hm)); auto.
Qed.

(** A fork with nothing open, running a body made for its herd, has what the body's closures ask. *)
Lemma main_of_extra {t h Γ} b : innermost Γ t h -> main_of h b -> plain b -> callable b -> extra t b Γ.
Proof.
  intros Hinn. induction b; cbn; trivial; try tauto.
  intros <- _ _. exact Hinn.
Qed.

Section WithInv.

  Variables (σ : jst) (Γ : gh).
  Hypothesis HI : Inv σ Γ.

  (** In a thread's open herds, each was opened inside those after it, and inside the herd the thread is a fork
      of. *)
  Lemma stack_anc u : forall post pre h, g_open Γ u = pre ++ h :: post ->
    (forall h2, In h2 post -> anc Γ h h2) /\
    (forall m b, g_role Γ u = ForkOf m b -> anc Γ h m).
  Proof.
    induction post as [| h1 post IH]; intros pre h Hsplit.
    - assert (Hin : In h (g_open Γ u)) by (rewrite Hsplit; apply in_or_app; right; left; trivial).
      apply (i_open HI) in Hin. destruct Hin as (hr & Hh & _).
      pose proof (i_stack HI Hsplit Hh) as Hp. split; [intros h2 []|].
      intros m b Hr. rewrite Hr in Hp. cbn in Hp. eapply anc_step; [exact Hh | exact Hp | constructor].
    - assert (Hin : In h (g_open Γ u)) by (rewrite Hsplit; apply in_or_app; right; left; trivial).
      apply (i_open HI) in Hin. destruct Hin as (hr & Hh & _).
      pose proof (i_stack HI Hsplit Hh) as Hp.
      assert (Hsplit' : g_open Γ u = (pre ++ [h]) ++ h1 :: post) by (rewrite <- app_assoc; exact Hsplit).
      destruct (IH _ _ Hsplit') as (IH1 & IH2).
      assert (Hstep : anc Γ h h1) by (eapply anc_step; [exact Hh | exact Hp | constructor]).
      split.
      + intros h2 [<- | Hin2]; [exact Hstep | exact (anc_trans Hstep (IH1 h2 Hin2))].
      + intros m b Hr. exact (anc_trans Hstep (IH2 m b Hr)).
  Qed.

  (** Every herd a thread is inside encloses, or is, the one it is most deeply inside. *)
  Theorem inner_anc t h X : innermost Γ t h -> inside Γ t X -> anc Γ h X.
  Proof.
    unfold innermost. intros Hinn (h0 & Hb & Ha).
    destruct (g_open Γ t) as [| h' rest] eqn:Eo.
    - destruct Hinn as ((b & Hb1) & _). destruct Hb as [((b' & Hb') & _) | Hin].
      + rewrite Hb1 in Hb'. injection Hb' as <- _. exact Ha.
      + rewrite Eo in Hin. contradiction.
    - subst h'. destruct (stack_anc t rest [] h Eo) as (S1 & S2).
      eapply anc_trans; [| exact Ha]. destruct Hb as [((b' & Hb') & _) | Hin].
      + exact (S2 _ _ Hb').
      + rewrite Eo in Hin. destruct Hin as [<- | Hin]; [constructor | exact (S1 _ Hin)].
  Qed.

  (** A thread's open herds were all opened after the herd it is a fork of. *)
  Lemma stack_stamp u m b : g_role Γ u = ForkOf m b ->
    forall post pre h hr, g_open Γ u = pre ++ h :: post -> g_herd Γ h = Some hr ->
    exists hrm, g_herd Γ m = Some hrm /\ h_stamp hrm < h_stamp hr.
  Proof.
    intro Hr. induction post as [| h1 post IH]; intros pre h hr Hsplit Hh.
    - pose proof (i_stack HI Hsplit Hh) as Hp. rewrite Hr in Hp. cbn in Hp.
      exact (i_stamp HI Hh Hp).
    - pose proof (i_stack HI Hsplit Hh) as Hp.
      destruct (i_stamp HI Hh Hp) as (hr1 & Hh1 & Hlt).
      assert (Hsplit' : g_open Γ u = (pre ++ [h]) ++ h1 :: post) by (rewrite <- app_assoc; exact Hsplit).
      destruct (IH _ _ _ Hsplit' Hh1) as (hrm & Hm & Hlt'). exists hrm. split; [exact Hm | lia].
  Qed.

  (** When the first thread owns no open herd, no herd is open. *)
  Lemma no_open_herd : g_open Γ main = [] -> forall n h hr, g_herd Γ h = Some hr -> h_stamp hr = n ->
    h_exited hr = true.
  Proof.
    intro Hmain. induction n as [n IH] using lt_wf_ind. intros h hr Hh Hn.
    destruct (h_exited hr) eqn:Ex; trivial. exfalso.
    assert (Hin : In h (g_open Γ (h_owner hr))) by (apply (i_open HI); exists hr; auto).
    set (o := h_owner hr) in *.
    assert (Hne : g_open Γ o <> []) by (intro E; rewrite E in Hin; contradiction).
    assert (Hb : begun σ o).
    { destruct (begun_dec σ o) as [Hb | Hnb]; trivial. destruct (i_new HI Hnb) as (_ & E). contradiction. }
    destruct (i_started HI Hb) as [Hm | (m & b & Hr)].
    - apply (i_main HI) in Hm. rewrite Hm in Hne. contradiction.
    - destruct (in_split _ _ Hin) as (pre & post & Hsplit).
      destruct (stack_stamp o m b Hr post pre h hr Hsplit Hh) as (hrm & Hm & Hlt).
      assert (Hrm : g_removed Γ o = false).
      { destruct (g_removed Γ o) eqn:E; trivial. destruct (i_removed HI E) as (E' & _). contradiction. }
      destruct (member_open HI Hr Hrm) as (hrm' & Hm' & Hexm). rewrite Hm in Hm'. injection Hm' as <-.
      assert (Hexm' : h_exited hrm = true) by (eapply (IH (h_stamp hrm)); [lia | exact Hm | reflexivity]).
      congruence.
  Qed.

  (** Then every fork has taken itself out of its herd's set. *)
  Theorem all_removed : g_open Γ main = [] -> forall u h b, g_role Γ u = ForkOf h b -> g_removed Γ u = true.
  Proof.
    intros Hmain u h b Hr. destruct (g_removed Γ u) eqn:E; trivial. exfalso.
    destruct (member_open HI Hr E) as (hr & Hh & Hex).
    rewrite (no_open_herd Hmain (h_stamp hr) h hr Hh eq_refl) in Hex. discriminate.
  Qed.

End WithInv.
