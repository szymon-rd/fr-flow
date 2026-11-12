(** The steps that change what the invariant reads, each with the ghost state it leaves and the proof that the
    invariant holds again. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Code Ox.Ghost Ox.Facts Ox.Specs Ox.Frame.
Import ListNotations.
Open Scope list_scope.

Definition set_herd (Γ : gh) (h : nat) (hr : hrec) : gh :=
  mkG (upd (g_herd Γ) h (Some hr)) (g_role Γ) (g_removed Γ) (g_open Γ) (g_fin Γ) (g_clock Γ).
Definition set_role (Γ : gh) (u : tid) (r : role) : gh :=
  mkG (g_herd Γ) (upd (g_role Γ) u r) (g_removed Γ) (g_open Γ) (g_fin Γ) (g_clock Γ).
Definition set_removed (Γ : gh) (u : tid) : gh :=
  mkG (g_herd Γ) (g_role Γ) (upd (g_removed Γ) u true) (g_open Γ) (g_fin Γ) (g_clock Γ).
Definition set_open (Γ : gh) (u : tid) (l : list nat) : gh :=
  mkG (g_herd Γ) (g_role Γ) (g_removed Γ) (upd (g_open Γ) u l) (g_fin Γ) (g_clock Γ).
Definition set_fin (Γ : gh) (r : nat) : gh :=
  mkG (g_herd Γ) (g_role Γ) (g_removed Γ) (g_open Γ) (upd (g_fin Γ) r true) (g_clock Γ).

Ltac du :=
  repeat match goal with
    | |- context [Nat.eq_dec ?a ?b] => destruct (Nat.eq_dec a b); subst
    | H : context [Nat.eq_dec ?a ?b] |- _ => destruct (Nat.eq_dec a b); subst
    end.

Lemma begun_started (σ : jst) u : started σ u -> begun σ u.
Proof. unfold started, begun. destruct (j_th σ u) as [[c s i] |]; [destruct s |]; trivial. Qed.

Lemma begun_dec (σ : jst) u : begun σ u \/ ~ begun σ u.
Proof. unfold begun. destruct (j_th σ u) as [[c s i] |]; [destruct s |]; auto. Qed.

(** ** `ThreadFactory.newThread`: a thread made for a herd *)

Lemma inv_newthread σ Γ t u th b :
  Inv σ Γ -> j_th σ u = None ->
  Inv (set_th σ u (Thread (Lam_ThreadHerd_startThread_1 th b) TNew false)) (set_role Γ u (Created t th b)).
Proof.
  intros HI Hu. pose proof (i_none HI Hu) as Hrole.
  assert (Hfork1 : forall v h b', upd (g_role Γ) u (Created t th b) v = ForkOf h b' -> g_role Γ v = ForkOf h b').
  { intros v h b'. unfold upd. du; [discriminate | trivial]. }
  assert (Hfork2 : forall v h b', g_role Γ v = ForkOf h b' -> upd (g_role Γ) u (Created t th b) v = ForkOf h b').
  { intros v h b'. unfold upd. du; [rewrite Hrole; discriminate | trivial]. }
  assert (Hmain : forall v, upd (g_role Γ) u (Created t th b) v = Main -> g_role Γ v = Main).
  { intros v. unfold upd. du; [discriminate | trivial]. }
  assert (Hmem : forall v, member_herd (upd (g_role Γ) u (Created t th b) v) = member_herd (g_role Γ v)).
  { intros v. unfold upd. du; [rewrite Hrole; reflexivity | reflexivity]. }
  assert (Hbeg : forall v, begun (set_th σ u (Thread (Lam_ThreadHerd_startThread_1 th b) TNew false)) v -> begun σ v).
  { intros v. unfold begun. cbn. unfold upd. du; [contradiction | trivial]. }
  constructor; cbn.
  - intros h hr H. destruct (i_herd HI H) as (s & Hs & Hiff). exists s. split; trivial.
    intro v. rewrite (Hiff v). split; intros ((b' & Hb') & Hrm).
    + split; [exists b' | exact Hrm]. apply Hfork2. exact Hb'.
    + split; [exists b' | exact Hrm]. apply Hfork1. exact Hb'.
  - intros h hr H Hx v b' Hr. apply Hfork1 in Hr. exact (i_exit HI H Hx Hr).
  - intros v h. exact (i_open HI v h).
  - intro v. exact (i_nodup HI v).
  - intros v pre h post hr H1 H2. rewrite Hmem. exact (i_stack HI H1 H2).
  - intros h hr h1 H1 H2. exact (i_stamp HI H1 H2).
  - intros h hr H. exact (i_clock HI H).
  - intros v H. destruct (i_removed HI H) as (Ho & h & b' & Hr). split; trivial.
    exists h, b'. apply Hfork2. exact Hr.
  - intros v Hn. apply (i_new HI). intro Hb. apply Hn. unfold begun in *. cbn. unfold upd. du; trivial.
    rewrite Hu in Hb. contradiction.
  - intros v Hn. unfold upd in *. du; [discriminate |]. exact (i_none HI Hn).
  - intros v t' th' b' Hr. unfold upd in *. du.
    + injection Hr as <- <- <-. eauto.
    + exact (i_created HI Hr).
  - intros v h b' Hr. apply Hfork1 in Hr. destruct (i_fork HI Hr) as (Hreg & th' & st & i & E & Hth).
    split; trivial. exists th', st, i. split; trivial. unfold upd. du; [congruence | trivial].
  - intros v Hb. apply Hbeg in Hb. destruct (i_started HI Hb) as [Hm | (h & b' & Hr)].
    + left. unfold upd. du; [congruence | trivial].
    + right. exists h, b'. apply Hfork2. exact Hr.
  - intros v Hm. apply Hmain in Hm. exact (i_main HI Hm).
  - intros r H. exact (i_fin HI H).
  - intros (c & i & E). apply (i_done HI). unfold upd in E. du; [discriminate | eauto].
Qed.

Lemma guar_newthread σ Γ t u th b :
  Inv σ Γ -> j_th σ u = None -> Guar t Γ (set_role Γ u (Created t th b)).
Proof.
  intros HI Hu v Hv. pose proof (i_none HI Hu) as Hrole. constructor; cbn; trivial.
  - intros h hr H. exists hr. auto 10.
  - intros w h b' Hr. unfold upd. du; [congruence | trivial].
  - intros w Hr. unfold upd. du; [congruence | trivial].
  - intros w th' b' Hr. unfold upd. du; [congruence | trivial].
Qed.

Lemma upd_eq {B : Type} (f : nat -> B) k v : upd f k v k = v.
Proof. unfold upd. destruct (Nat.eq_dec k k); [trivial | contradiction]. Qed.

Lemma upd_neq {B : Type} (f : nat -> B) k v {x} : x <> k -> upd f k v x = f x.
Proof. intro H. unfold upd. destruct (Nat.eq_dec x k); [contradiction | trivial]. Qed.

(** ** `threads.add(thread)`: the thread becomes a fork of the herd *)

Lemma inv_add σ Γ t c th b h s :
  Inv σ Γ -> g_role Γ c = Created t th b -> ThreadHerd_threads th = h -> open_herd Γ h ->
  j_ts σ h = Some s ->
  Inv (set_ts σ h (upd s c true)) (set_role Γ c (ForkOf h b)).
Proof.
  intros HI Hc Hth (hr0 & Hh0 & Hex0) Hs.
  destruct (i_created HI Hc) as (i0 & Ec).
  assert (Hnb : ~ begun σ c) by (unfold begun; rewrite Ec; tauto).
  destruct (i_new HI Hnb) as (Hrmc & Hopc).
  assert (R1 : forall v h' b', upd (g_role Γ) c (ForkOf h b) v = ForkOf h' b' ->
            (v = c /\ h' = h /\ b' = b) \/ (v <> c /\ g_role Γ v = ForkOf h' b')).
  { intros v h' b'. unfold upd. du; intro E; [left; injection E as <- <-; auto | right; auto]. }
  assert (R2 : forall v h' b', g_role Γ v = ForkOf h' b' -> upd (g_role Γ) c (ForkOf h b) v = ForkOf h' b').
  { intros v h' b' E. unfold upd. du; [congruence | trivial]. }
  constructor; cbn.
  - (* i_herd *)
    intros h' hr H. destruct (i_herd HI H) as (s' & Hs' & Hiff).
    destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq. rewrite Hs in Hs'. injection Hs' as <-.
      exists (upd s c true). split; trivial. intro v.
      destruct (Nat.eq_dec v c) as [-> | Hvc].
      * rewrite !upd_eq. split; [intros _ | trivial]. split; [exists b; trivial | exact Hrmc].
      * rewrite (upd_neq s c true Hvc). rewrite (Hiff v). split; intros ((b' & Hb') & Hrm).
        -- split; [exists b'; apply R2; exact Hb' | exact Hrm].
        -- split; [| exact Hrm]. destruct (R1 _ _ _ Hb') as [(-> & _) | (_ & Hr)]; [contradiction | eauto].
    + rewrite (upd_neq (j_ts σ) h _ Hne). exists s'. split; trivial. intro v. rewrite (Hiff v).
      split; intros ((b' & Hb') & Hrm).
      * split; [exists b'; apply R2; exact Hb' | exact Hrm].
      * split; [| exact Hrm]. destruct (R1 _ _ _ Hb') as [(_ & -> & _) | (_ & Hr)]; [contradiction | eauto].
  - (* i_exit *)
    intros h' hr H Hx v b' Hr. destruct (R1 _ _ _ Hr) as [(-> & -> & _) | (_ & Hr')].
    + rewrite Hh0 in H. injection H as <-. congruence.
    + exact (i_exit HI H Hx Hr').
  - intros v h'. exact (i_open HI v h').
  - intro v. exact (i_nodup HI v).
  - (* i_stack *)
    intros v pre h' post hr H1 H2. destruct (Nat.eq_dec v c) as [-> | Hvc].
    + rewrite Hopc in H1. destruct pre; discriminate.
    + rewrite (upd_neq (g_role Γ) c _ Hvc). exact (i_stack HI H1 H2).
  - intros h' hr h1 H1 H2. exact (i_stamp HI H1 H2).
  - intros h' hr H. exact (i_clock HI H).
  - (* i_removed *)
    intros v H. destruct (i_removed HI H) as (Ho & h' & b' & Hr). split; trivial.
    exists h', b'. apply R2. exact Hr.
  - intros v Hn. apply (i_new HI). exact Hn.
  - intros v Hn. rewrite upd_neq; [exact (i_none HI Hn) | intros ->; congruence].
  - (* i_created *)
    intros v t' th' b' Hr. destruct (Nat.eq_dec v c) as [-> | Hvc].
    + rewrite upd_eq in Hr. discriminate.
    + rewrite (upd_neq (g_role Γ) c _ Hvc) in Hr. exact (i_created HI Hr).
  - (* i_fork *)
    intros v h' b' Hr. destruct (R1 _ _ _ Hr) as [(-> & -> & ->) | (_ & Hr')].
    + split; [congruence |]. exists th, TNew, i0. auto.
    + exact (i_fork HI Hr').
  - (* i_started *)
    intros v Hb. destruct (i_started HI Hb) as [Hm | (h' & b' & Hr)].
    + left. rewrite upd_neq; [exact Hm | intros ->; congruence].
    + right. exists h', b'. apply R2. exact Hr.
  - intros v Hm. destruct (Nat.eq_dec v c) as [-> | Hvc].
    + rewrite upd_eq in Hm. discriminate.
    + rewrite (upd_neq (g_role Γ) c _ Hvc) in Hm. exact (i_main HI Hm).
  - intros r H. exact (i_fin HI H).
  - exact (i_done HI).
Qed.

Lemma guar_add Γ t c th b h :
  g_role Γ c = Created t th b -> Guar t Γ (set_role Γ c (ForkOf h b)).
Proof.
  intros Hc v Hv. constructor; cbn; trivial.
  - intros h' hr H. exists hr. auto 10.
  - intros w h' b' Hr. rewrite upd_neq; [trivial | intros ->; congruence].
  - intros w Hr. rewrite upd_neq; [trivial | intros ->; congruence].
  - intros w th' b' Hr. rewrite upd_neq; [trivial | intros ->; congruence].
Qed.

(** ** `thread.start()`: a fork starts *)

Lemma inv_start σ Γ c code0 i h b :
  Inv σ Γ -> j_th σ c = Some (Thread code0 TNew i) -> g_role Γ c = ForkOf h b ->
  Inv (set_th σ c (Thread code0 TStarted i)) Γ.
Proof.
  intros HI Ec Hc.
  assert (Hbeg : forall v, v <> c -> begun (set_th σ c (Thread code0 TStarted i)) v -> begun σ v).
  { intros v Hv. unfold begun. cbn. rewrite (upd_neq (j_th σ) c _ Hv). trivial. }
  constructor; cbn.
  - intros h' hr H. exact (i_herd HI H).
  - intros h' hr H Hx u b' Hr. exact (i_exit HI H Hx Hr).
  - intros u h'. exact (i_open HI u h').
  - intro u. exact (i_nodup HI u).
  - intros u pre h' post hr H1 H2. exact (i_stack HI H1 H2).
  - intros h' hr h1 H1 H2. exact (i_stamp HI H1 H2).
  - intros h' hr H. exact (i_clock HI H).
  - intros u H. exact (i_removed HI H).
  - intros u Hn. destruct (Nat.eq_dec u c) as [-> | Hu].
    + exfalso. apply Hn. unfold begun. cbn. rewrite upd_eq. trivial.
    + apply (i_new HI). intro Hb. apply Hn. unfold begun in *. cbn. rewrite (upd_neq (j_th σ) c _ Hu). trivial.
  - intros u Hn. destruct (Nat.eq_dec u c) as [-> | Hu].
    + rewrite upd_eq in Hn. discriminate.
    + rewrite (upd_neq (j_th σ) c _ Hu) in Hn. exact (i_none HI Hn).
  - intros u t th b' Hr. destruct (Nat.eq_dec u c) as [-> | Hu]; [congruence |].
    rewrite (upd_neq (j_th σ) c _ Hu). exact (i_created HI Hr).
  - intros u h' b' Hr. destruct (i_fork HI Hr) as (Hreg & th & st & i' & E & Hth). split; trivial.
    destruct (Nat.eq_dec u c) as [-> | Hu].
    + rewrite upd_eq. rewrite Ec in E. injection E as -> _ _. exists th, TStarted, i. auto.
    + rewrite (upd_neq (j_th σ) c _ Hu). eauto.
  - intros u Hb. destruct (Nat.eq_dec u c) as [-> | Hu]; [eauto |].
    exact (i_started HI (Hbeg u Hu Hb)).
  - intros u H. exact (i_main HI H).
  - intros r H. exact (i_fin HI H).
  - intros (c' & i' & E). apply (i_done HI). destruct (Nat.eq_dec main c) as [Hm | Hm].
    + rewrite Hm, upd_eq in E. discriminate.
    + rewrite (upd_neq (j_th σ) c _ Hm) in E. eauto.
Qed.

(** ** `threads.remove(Thread.currentThread())`: a fork takes itself out *)

Lemma inv_remove σ Γ u h b s :
  Inv σ Γ -> started σ u -> g_role Γ u = ForkOf h b -> g_open Γ u = [] -> j_ts σ h = Some s ->
  Inv (set_ts σ h (upd s u false)) (set_removed Γ u).
Proof.
  intros HI Hst Hr Hop Hs.
  constructor; cbn.
  - (* i_herd *)
    intros h' hr H. destruct (i_herd HI H) as (s' & Hs' & Hiff).
    destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq. rewrite Hs in Hs'. injection Hs' as <-.
      exists (upd s u false). split; trivial. intro v.
      destruct (Nat.eq_dec v u) as [-> | Hv].
      * rewrite !upd_eq. split; [discriminate | intros (_ & E); discriminate].
      * rewrite (upd_neq s u false Hv), (upd_neq (g_removed Γ) u true Hv). exact (Hiff v).
    + rewrite (upd_neq (j_ts σ) h _ Hne). exists s'. split; trivial. intro v.
      destruct (Nat.eq_dec v u) as [-> | Hv].
      * rewrite upd_eq. rewrite (Hiff u). split; [| intros (_ & E); discriminate].
        intros ((b' & Hb') & _). congruence.
      * rewrite (upd_neq (g_removed Γ) u true Hv). exact (Hiff v).
  - (* i_exit *)
    intros h' hr H Hx v b' Hv. destruct (Nat.eq_dec v u) as [-> | Hne]; [apply upd_eq |].
    rewrite (upd_neq (g_removed Γ) u true Hne). exact (i_exit HI H Hx Hv).
  - intros v h'. exact (i_open HI v h').
  - intro v. exact (i_nodup HI v).
  - intros v pre h' post hr H1 H2. exact (i_stack HI H1 H2).
  - intros h' hr h1 H1 H2. exact (i_stamp HI H1 H2).
  - intros h' hr H. exact (i_clock HI H).
  - (* i_removed *)
    intros v H. destruct (Nat.eq_dec v u) as [-> | Hne]; [eauto |].
    rewrite (upd_neq (g_removed Γ) u true Hne) in H. exact (i_removed HI H).
  - (* i_new *)
    intros v Hn. destruct (Nat.eq_dec v u) as [-> | Hne].
    + exfalso. apply Hn. apply begun_started. exact Hst.
    + rewrite (upd_neq (g_removed Γ) u true Hne). exact (i_new HI Hn).
  - intros v Hn. exact (i_none HI Hn).
  - intros v t th b' H. exact (i_created HI H).
  - intros v h' b' H. exact (i_fork HI H).
  - intros v Hb. exact (i_started HI Hb).
  - intros v H. exact (i_main HI H).
  - intros r H. exact (i_fin HI H).
  - exact (i_done HI).
Qed.

Lemma guar_remove Γ u : Guar u Γ (set_removed Γ u).
Proof.
  intros v Hv. constructor; cbn; trivial.
  - intros h hr H. exists hr. auto 10.
  - apply upd_neq. exact Hv.
Qed.

(** ** `ConcurrentHashMap.newKeySet()` in `ThreadHerd`'s constructor: a herd is opened *)

Definition parent_of (Γ : gh) (t : tid) : option nat :=
  match g_open Γ t with h1 :: _ => Some h1 | [] => member_herd (g_role Γ t) end.

Definition register (Γ : gh) (t : tid) (h : nat) : gh :=
  mkG (upd (g_herd Γ) h (Some (mkH t false (parent_of Γ t) (g_clock Γ)))) (g_role Γ) (g_removed Γ)
      (upd (g_open Γ) t (h :: g_open Γ t)) (g_fin Γ) (S (g_clock Γ)).

Lemma unregistered {σ Γ h} : Inv σ Γ -> j_ts σ h = None -> g_herd Γ h = None.
Proof.
  intros HI Hn. destruct (g_herd Γ h) as [hr |] eqn:E; trivial.
  destruct (i_herd HI E) as (s & Hs & _). congruence.
Qed.

Lemma inv_register σ Γ t h :
  Inv σ Γ -> started σ t -> g_removed Γ t = false -> j_ts σ h = None ->
  Inv (set_ts σ h (fun _ => false)) (register Γ t h).
Proof.
  intros HI Hst Hrm Hn. pose proof (unregistered HI Hn) as Hun.
  assert (Hnotin : forall u, ~ In h (g_open Γ u)).
  { intros u Hin. apply (i_open HI) in Hin. destruct Hin as (hr & E & _). congruence. }
  constructor; cbn.
  - (* i_herd *)
    intros h' hr H. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq. exists (fun _ => false). split; trivial. intro v. split; [discriminate |].
      intros ((b & Hb) & _). destruct (i_fork HI Hb) as (Hreg & _). contradiction.
    + rewrite (upd_neq (g_herd Γ) h _ Hne) in H. rewrite (upd_neq (j_ts σ) h _ Hne). exact (i_herd HI H).
  - (* i_exit *)
    intros h' hr H Hx v b Hv. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq in H. injection H as <-. discriminate.
    + rewrite (upd_neq (g_herd Γ) h _ Hne) in H. exact (i_exit HI H Hx Hv).
  - (* i_open *)
    intros u h'. destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite upd_eq. destruct (Nat.eq_dec h' h) as [-> | Hne].
      * rewrite upd_eq. split; [intros _ | intros _; left; trivial]. eexists. split; [reflexivity | auto].
      * rewrite (upd_neq (g_herd Γ) h _ Hne). rewrite <- (i_open HI t h'). cbn. split; [| auto].
        intros [E | Hin]; [congruence | trivial].
    + rewrite (upd_neq (g_open Γ) t _ Hu). destruct (Nat.eq_dec h' h) as [-> | Hne].
      * rewrite upd_eq. split; [intro Hin; exfalso; eapply Hnotin; eauto |].
        intros (hr & E & Ho & _). injection E as <-. cbn in Ho. congruence.
      * rewrite (upd_neq (g_herd Γ) h _ Hne). exact (i_open HI u h').
  - (* i_nodup *)
    intro u. destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite upd_eq. constructor; [apply Hnotin | exact (i_nodup HI t)].
    + rewrite (upd_neq (g_open Γ) t _ Hu). exact (i_nodup HI u).
  - (* i_stack *)
    intros u pre h' post hr H1 H2. destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite upd_eq in H1. destruct pre as [| p pre'].
      * cbn in H1. injection H1 as <- <-. rewrite upd_eq in H2. injection H2 as <-. reflexivity.
      * cbn in H1. injection H1 as <- H1.
        assert (Hne : h' <> h).
        { intros ->. apply (Hnotin t). rewrite H1. apply in_or_app. right. left. trivial. }
        rewrite (upd_neq (g_herd Γ) h _ Hne) in H2. exact (i_stack HI H1 H2).
    + rewrite (upd_neq (g_open Γ) t _ Hu) in H1.
      assert (Hne : h' <> h).
      { intros ->. apply (Hnotin u). rewrite H1. apply in_or_app. right. left. trivial. }
      rewrite (upd_neq (g_herd Γ) h _ Hne) in H2. exact (i_stack HI H1 H2).
  - (* i_stamp *)
    intros h' hr h1 H1 H2. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq in H1. injection H1 as <-. cbn in H2. cbn.
      assert (Hreg : exists hr1, g_herd Γ h1 = Some hr1).
      { unfold parent_of in H2. destruct (g_open Γ t) as [| h1' rest] eqn:Eo.
        - destruct (g_role Γ t) as [| | | h0 b0] eqn:Er; cbn in H2; try discriminate.
          injection H2 as E2. subst h0.
          destruct (i_fork HI Er) as (Hreg & _). destruct (g_herd Γ h1); [eauto | contradiction].
        - injection H2 as E2. subst h1'.
          assert (Hin : In h1 (g_open Γ t)) by (rewrite Eo; left; trivial).
          apply (i_open HI) in Hin. destruct Hin as (hr1 & E & _). eauto. }
      destruct Hreg as (hr1 & E1). exists hr1. split; [| exact (i_clock HI E1)].
      rewrite upd_neq; [exact E1 | intros ->; congruence].
    + rewrite (upd_neq (g_herd Γ) h _ Hne) in H1. destruct (i_stamp HI H1 H2) as (hr1 & E1 & Hlt).
      exists hr1. split; [| exact Hlt]. rewrite upd_neq; [exact E1 | intros ->; congruence].
  - (* i_clock *)
    intros h' hr H. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq in H. injection H as <-. cbn. lia.
    + rewrite (upd_neq (g_herd Γ) h _ Hne) in H. pose proof (i_clock HI H). lia.
  - (* i_removed *)
    intros u H. destruct (Nat.eq_dec u t) as [-> | Hu]; [congruence |].
    rewrite (upd_neq (g_open Γ) t _ Hu). exact (i_removed HI H).
  - (* i_new *)
    intros u Hnb. destruct (Nat.eq_dec u t) as [-> | Hu].
    + exfalso. apply Hnb. apply begun_started in Hst. exact Hst.
    + rewrite (upd_neq (g_open Γ) t _ Hu). exact (i_new HI Hnb).
  - intros u Hu. exact (i_none HI Hu).
  - intros u t' th b H. exact (i_created HI H).
  - (* i_fork *)
    intros u h' b H. destruct (i_fork HI H) as (Hreg & Hrest). split; [| exact Hrest].
    destruct (Nat.eq_dec h' h) as [-> | Hne]; [rewrite upd_eq; discriminate |].
    rewrite (upd_neq (g_herd Γ) h _ Hne). exact Hreg.
  - intros u Hb. exact (i_started HI Hb).
  - intros u H. exact (i_main HI H).
  - intros r H. exact (i_fin HI H).
  - (* i_done *)
    intros (c & i & E). destruct (Nat.eq_dec main t) as [Hm | Hm].
    + exfalso. unfold started in Hst. rewrite <- Hm, E in Hst. exact Hst.
    + rewrite (upd_neq (g_open Γ) t _ Hm). apply (i_done HI). eauto.
Qed.

Lemma guar_register σ Γ t h : Inv σ Γ -> j_ts σ h = None -> Guar t Γ (register Γ t h).
Proof.
  intros HI Hn v Hv. pose proof (unregistered HI Hn) as Hun. constructor; cbn; trivial.
  - intros h' hr H. exists hr. rewrite upd_neq; [auto 10 | intros ->; congruence].
  - apply upd_neq. exact Hv.
Qed.

(** ** `threads.isEmpty` answering `true` in the closing loop: the herd is exited *)

Definition exit_herd (Γ : gh) (t : tid) (h : nat) (hr : hrec) (rest : list nat) : gh :=
  mkG (upd (g_herd Γ) h (Some (mkH (h_owner hr) true (h_parent hr) (h_stamp hr)))) (g_role Γ) (g_removed Γ)
      (upd (g_open Γ) t rest) (g_fin Γ) (g_clock Γ).

Lemma inv_exit σ Γ t h hr rest s :
  Inv σ Γ -> started σ t -> g_open Γ t = h :: rest -> g_herd Γ h = Some hr ->
  j_ts σ h = Some s -> (forall u, s u = false) ->
  Inv σ (exit_herd Γ t h hr rest).
Proof.
  intros HI Hst Hop Hh Hs Hempty.
  assert (Hin : In h (g_open Γ t)) by (rewrite Hop; left; trivial).
  pose proof Hin as Hin'. apply (i_open HI) in Hin'. destruct Hin' as (hr' & E' & Hown & Hnex).
  rewrite Hh in E'. injection E' as <-.
  pose proof (i_nodup HI t) as Hnd. rewrite Hop in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
  constructor; cbn.
  - (* i_herd *)
    intros h' hr' H. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + exact (i_herd HI Hh).
    + rewrite (upd_neq (g_herd Γ) h _ Hne) in H. exact (i_herd HI H).
  - (* i_exit *)
    intros h' hr' H Hx v b Hv. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + destruct (i_herd HI Hh) as (s' & Hs' & Hiff). rewrite Hs in Hs'. injection Hs' as <-.
      destruct (g_removed Γ v) eqn:Erm; trivial.
      assert (Hsv : s v = true) by (apply Hiff; eauto). rewrite Hempty in Hsv. discriminate.
    + rewrite (upd_neq (g_herd Γ) h _ Hne) in H. exact (i_exit HI H Hx Hv).
  - (* i_open *)
    intros u h'. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq. split.
      * intro Hi. exfalso. destruct (Nat.eq_dec u t) as [-> | Hu].
        -- rewrite upd_eq in Hi. contradiction.
        -- rewrite (upd_neq (g_open Γ) t _ Hu) in Hi. apply (i_open HI) in Hi.
           destruct Hi as (hr2 & E2 & Ho2 & _). rewrite Hh in E2. injection E2 as <-. congruence.
      * intros (hr2 & E2 & _ & Hx). injection E2 as <-. discriminate.
    + rewrite (upd_neq (g_herd Γ) h _ Hne). rewrite <- (i_open HI u h').
      destruct (Nat.eq_dec u t) as [-> | Hu].
      * rewrite upd_eq, Hop. cbn. split; [auto | intros [E | Hi]; [congruence | trivial]].
      * rewrite (upd_neq (g_open Γ) t _ Hu). tauto.
  - (* i_nodup *)
    intro u. destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite upd_eq. exact Hnd'.
    + rewrite (upd_neq (g_open Γ) t _ Hu). exact (i_nodup HI u).
  - (* i_stack *)
    intros u pre h' post hr2 H1 H2.
    assert (Hne : h' <> h).
    { intros ->. destruct (Nat.eq_dec u t) as [-> | Hu].
      - rewrite upd_eq in H1. apply Hnotin. rewrite H1. apply in_or_app. right. left. trivial.
      - rewrite (upd_neq (g_open Γ) t _ Hu) in H1.
        assert (Hi : In h (g_open Γ u)) by (rewrite H1; apply in_or_app; right; left; trivial).
        apply (i_open HI) in Hi. destruct Hi as (hr3 & E3 & Ho3 & _).
        rewrite Hh in E3. injection E3 as <-. congruence. }
    rewrite (upd_neq (g_herd Γ) h _ Hne) in H2.
    destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite upd_eq in H1.
      assert (H1' : g_open Γ t = (h :: pre) ++ h' :: post) by (rewrite Hop, H1; reflexivity).
      exact (i_stack HI H1' H2).
    + rewrite (upd_neq (g_open Γ) t _ Hu) in H1. exact (i_stack HI H1 H2).
  - (* i_stamp *)
    intros h' hr2 h1 H1 H2.
    assert (Hold : exists hr0, g_herd Γ h' = Some hr0 /\ h_parent hr0 = Some h1 /\ h_stamp hr0 = h_stamp hr2).
    { destruct (Nat.eq_dec h' h) as [-> | Hne].
      - rewrite upd_eq in H1. injection H1 as <-. cbn in H2. eauto.
      - rewrite (upd_neq (g_herd Γ) h _ Hne) in H1. eauto. }
    destruct Hold as (hr0 & E0 & Hp0 & Hs0). destruct (i_stamp HI E0 Hp0) as (hr1 & E1 & Hlt).
    destruct (Nat.eq_dec h1 h) as [-> | Hne1].
    + rewrite upd_eq. eexists. split; [reflexivity |]. cbn. rewrite Hh in E1. injection E1 as <-. lia.
    + rewrite (upd_neq (g_herd Γ) h _ Hne1). exists hr1. split; [exact E1 | lia].
  - (* i_clock *)
    intros h' hr2 H. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq in H. injection H as <-. cbn. exact (i_clock HI Hh).
    + rewrite (upd_neq (g_herd Γ) h _ Hne) in H. exact (i_clock HI H).
  - (* i_removed *)
    intros u H. destruct (i_removed HI H) as (Ho & Hr). split; [| exact Hr].
    destruct (Nat.eq_dec u t) as [-> | Hu]; [congruence |].
    rewrite (upd_neq (g_open Γ) t _ Hu). exact Ho.
  - (* i_new *)
    intros u Hnb. destruct (Nat.eq_dec u t) as [-> | Hu].
    + exfalso. apply Hnb. apply begun_started. exact Hst.
    + rewrite (upd_neq (g_open Γ) t _ Hu). exact (i_new HI Hnb).
  - intros u Hu. exact (i_none HI Hu).
  - intros u t' th b H. exact (i_created HI H).
  - (* i_fork *)
    intros u h' b H. destruct (i_fork HI H) as (Hreg & Hrest). split; [| exact Hrest].
    destruct (Nat.eq_dec h' h) as [-> | Hne]; [rewrite upd_eq; discriminate |].
    rewrite (upd_neq (g_herd Γ) h _ Hne). exact Hreg.
  - intros u Hb. exact (i_started HI Hb).
  - intros u H. exact (i_main HI H).
  - intros r H. exact (i_fin HI H).
  - (* i_done *)
    intros (c & i & E). destruct (Nat.eq_dec main t) as [Hm | Hm].
    + exfalso. unfold started in Hst. rewrite <- Hm, E in Hst. exact Hst.
    + rewrite (upd_neq (g_open Γ) t _ Hm). apply (i_done HI). eauto.
Qed.

Lemma guar_exit Γ t h hr rest : g_herd Γ h = Some hr -> h_owner hr = t -> Guar t Γ (exit_herd Γ t h hr rest).
Proof.
  intros Hh Ho v Hv. constructor; cbn; trivial.
  - intros h' hr' H. destruct (Nat.eq_dec h' h) as [-> | Hne].
    + rewrite upd_eq. rewrite Hh in H. injection H as <-. eexists. split; [reflexivity |]. cbn.
      repeat split; trivial. intro E. congruence.
    + rewrite (upd_neq (g_herd Γ) h _ Hne). exists hr'. auto 10.
  - apply upd_neq. exact Hv.
Qed.

(** ** A scope's finalizers: `new AtomicReference(Nil)`, and `getAndSet(null)` *)

Lemma inv_arnew σ Γ r :
  Inv σ Γ -> Inv (set_ar σ r (Some (VList []))) (set_fin Γ r).
Proof.
  intros HI.
  pose proof HI as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  constructor; cbn; try assumption.
  intros r' H. destruct (Nat.eq_dec r' r) as [-> | Hne].
  - rewrite upd_eq. right. trivial.
  - rewrite (upd_neq (g_fin Γ) r true Hne) in H. rewrite (upd_neq (j_ar σ) r _ Hne). exact (A15 r' H).
Qed.

Lemma guar_arnew Γ t r : Guar t Γ (set_fin Γ r).
Proof.
  intros v Hv. constructor; cbn; trivial.
  - intros h hr H. exists hr. auto 10.
  - intros r' H. unfold upd. destruct (Nat.eq_dec r' r); trivial.
Qed.

Lemma inv_artake σ Γ r :
  Inv σ Γ -> g_fin Γ r = true -> Inv (set_ar σ r None) Γ.
Proof.
  intros HI Hr.
  pose proof HI as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  constructor; cbn; try assumption.
  intros r' H. destruct (Nat.eq_dec r' r) as [-> | Hne].
  - rewrite upd_eq. left. trivial.
  - rewrite (upd_neq (j_ar σ) r _ Hne). exact (A15 r' H).
Qed.

(** ** A thread's end *)

Lemma inv_terminate σ Γ t :
  Inv σ Γ -> started σ t -> g_open Γ t = [] -> Inv (terminate σ t) Γ.
Proof.
  intros HI Hst Hop. unfold terminate. unfold started in Hst.
  destruct (j_th σ t) as [[c s i] |] eqn:Et; [| contradiction]. destruct s; try contradiction.
  assert (Hbeg : forall v, begun (set_th σ t (Thread c TTerminated i)) v <-> begun σ v).
  { intro v. unfold begun. cbn. destruct (Nat.eq_dec v t) as [-> | Hv].
    - rewrite upd_eq, Et. tauto.
    - rewrite (upd_neq (j_th σ) t _ Hv). tauto. }
  constructor; cbn.
  - intros h hr H. exact (i_herd HI H).
  - intros h hr H Hx u b Hr. exact (i_exit HI H Hx Hr).
  - intros u h. exact (i_open HI u h).
  - intro u. exact (i_nodup HI u).
  - intros u pre h post hr H1 H2. exact (i_stack HI H1 H2).
  - intros h hr h1 H1 H2. exact (i_stamp HI H1 H2).
  - intros h hr H. exact (i_clock HI H).
  - intros u H. exact (i_removed HI H).
  - intros u Hn. apply (i_new HI). intro Hb. apply Hn. apply Hbeg. exact Hb.
  - intros u Hn. destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite upd_eq in Hn. discriminate.
    + rewrite (upd_neq (j_th σ) t _ Hu) in Hn. exact (i_none HI Hn).
  - intros u t' th b Hr. destruct (i_created HI Hr) as (i' & E). destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite Et in E. discriminate.
    + rewrite (upd_neq (j_th σ) t _ Hu). eauto.
  - intros u h b Hr. destruct (i_fork HI Hr) as (Hreg & th & st & i' & E & Hth). split; trivial.
    destruct (Nat.eq_dec u t) as [-> | Hu].
    + rewrite upd_eq. rewrite Et in E. injection E as -> _ _. exists th, TTerminated, i. auto.
    + rewrite (upd_neq (j_th σ) t _ Hu). eauto.
  - intros u Hb. apply (i_started HI). apply Hbeg. exact Hb.
  - intros u H. exact (i_main HI H).
  - intros r H. exact (i_fin HI H).
  - intros (c' & i' & E). destruct (Nat.eq_dec main t) as [Hm | Hm].
    + rewrite Hm. exact Hop.
    + rewrite (upd_neq (j_th σ) t _ Hm) in E. apply (i_done HI). eauto.
Qed.
