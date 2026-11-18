(** What every step of the machine keeps.

    A run of the machine (`Frames.run_frames`) is a sequence of steps, each of one thread (`move`), from one
    configuration to the next (`trace`). Here is what holds of every configuration a run reaches (`inv`):

    - the calls of a thread were made at moments before now, each after the one that waits under it;
    - no two threads are the same thread, and each has been started;
    - the references name each value once, and each object named is in the heap, of the class it is named with.

    None of this is about the code: it is how the machine keeps its threads, its calls and its references. The
    laws of an execution are proven with it (`Bridge`). *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Scala.Run.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Rules.Walk FrFlow.Code.Witness.
Require Import FrFlow.Bridge.Names FrFlow.Bridge.Checks FrFlow.Bridge.Frames FrFlow.Bridge.Steps.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** ** Lists with one place replaced *)

Lemma in_firstn {A : Type} (n : nat) (xs : list A) (x : A) : In x (firstn n xs) -> In x xs.
Proof.
  revert n. induction xs as [| y ys IH]; intros [| n] H; cbn in *; try contradiction.
  destruct H as [-> | H]; [left; reflexivity | right; eauto].
Qed.

Lemma in_skipn {A : Type} (n : nat) (xs : list A) (x : A) : In x (skipn n xs) -> In x xs.
Proof.
  revert n. induction xs as [| y ys IH]; intros [| n] H; cbn in *; try contradiction; auto.
  right. eauto.
Qed.

Lemma split_nth {A : Type} (xs : list A) (n : nat) (x : A) :
  nth_error xs n = Some x -> xs = firstn n xs ++ x :: skipn (S n) xs.
Proof.
  revert n. induction xs as [| y ys IH]; intros [| n] H; cbn in *; try discriminate.
  - injection H as <-. reflexivity.
  - f_equal. apply IH, H.
Qed.

(** What is in a list with one place replaced and some added: the new one, one that was there, or one added. *)
Lemma in_replaced {A : Type} (xs new : list A) (n : nat) (y x : A) :
  In x (firstn n xs ++ y :: skipn (S n) xs ++ new) -> x = y \/ In x xs \/ In x new.
Proof.
  intros H. apply in_app_or in H as [H | [<- | H]].
  - right. left. exact (in_firstn _ _ _ H).
  - left. reflexivity.
  - apply in_app_or in H as [H | H]; [right; left; exact (in_skipn _ _ _ H) | right; right; exact H].
Qed.

Lemma nth_replaced {A : Type} (xs new : list A) (n : nat) (old y : A) :
  nth_error xs n = Some old -> nth_error (firstn n xs ++ y :: skipn (S n) xs ++ new) n = Some y.
Proof.
  intros H. assert (List.length (firstn n xs) = n) as L.
  { apply firstn_length_le. apply Nat.lt_le_incl. apply nth_error_Some. rewrite H. discriminate. }
  rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. reflexivity.
Qed.

Lemma nth_kept {A : Type} (xs new : list A) (n m : nat) (y x : A) :
  m <> n -> nth_error xs m = Some x -> nth_error (firstn n xs ++ y :: skipn (S n) xs ++ new) m = Some x.
Proof.
  revert n m. induction xs as [| z zs IH]; intros n m Hne H; [destruct m; discriminate H |].
  destruct n as [| n], m as [| m]; cbn in *; try congruence.
  - rewrite nth_error_app1; [exact H | apply nth_error_Some; rewrite H; discriminate].
  - apply IH; [congruence | exact H].
Qed.

(** ** What the operations leave *)

Definition tid_of (th : thread) : tid := match th with Active t _ _ _ | Done t _ => t end.

Ltac crack H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate H
  end;
  try (injection H as <- <-).

Definition was_started (σ : state) (u : tid) : Prop :=
  exists thr, s_th σ u = Some thr /\ t_status thr <> TNew.

Lemma started_clear (σ : state) (t u : tid) : was_started σ u -> was_started (clear_intr σ t) u.
Proof.
  intros (thr & H & Hs). unfold clear_intr. destruct (s_th σ t) as [th |] eqn:E; [| exists thr; auto].
  unfold was_started, set_th. cbn [s_th]. unfold upd. destruct (Nat.eq_dec u t) as [-> |]; [| exists thr; auto].
  rewrite E in H. injection H as <-. eexists. split; [reflexivity | exact Hs].
Qed.

Lemma started_terminate (σ : state) (t u : tid) : was_started σ u -> was_started (terminate σ t) u.
Proof.
  intros (thr & H & Hs). unfold terminate. destruct (s_th σ t) as [th |] eqn:E; [| exists thr; auto].
  unfold was_started, set_th. cbn [s_th]. unfold upd. destruct (Nat.eq_dec u t) as [-> |]; [| exists thr; auto].
  eexists. split; [reflexivity | discriminate].
Qed.

(** A thread that has been started stays so. *)
Lemma oprun_started (t : tid) (nxt : nat) (X : Type) (o : op X) (σ σ' : state) (x : X) (u : tid) :
  oprun t nxt o σ = Did x σ' -> was_started σ u -> was_started σ' u.
Proof.
  intros H Hu. destruct o; cbn in H; unfold waiting in H; crack H;
    try exact Hu; try (apply started_clear; exact Hu);
    try (destruct Hu as (thr & Hthr & Hs); unfold was_started, set_th, set_obj, set_ext; cbn [s_th]; unfold upd;
         match goal with |- context [Nat.eq_dec u ?k] => destruct (Nat.eq_dec u k) as [-> |] end;
         [| exists thr; auto]).
  all: try congruence.
  all: try (eexists; split; [reflexivity | cbn; first [discriminate | congruence]]).
  all: rewrite Heqo in Hthr; injection Hthr as <-; eexists; split; [reflexivity | exact Hs].
Qed.

(** An operation starts no thread, or one that was made and not started. *)
Lemma started_one (σ : state) (X : Type) (o : op X) :
  started σ o = [] \/ exists u c i, started σ o = [root u c] /\ s_th σ u = Some (Thread c TNew i).
Proof.
  destruct o; try (left; reflexivity). cbn. destruct (s_th σ u) as [[c [] i] |] eqn:E; try (left; reflexivity).
  right. exists u, c, i. auto.
Qed.

(** A thread an operation starts was not started, and is after it. *)
Lemma started_fresh (t : tid) (nxt : nat) (X : Type) (o : op X) (σ σ' : state) (x : X) (th : thread) :
  oprun t nxt o σ = Did x σ' -> In th (started σ o) ->
  ~ was_started σ (tid_of th) /\ was_started σ' (tid_of th) /\ exists c, th = root (tid_of th) c.
Proof.
  intros H Hin. destruct o; try (destruct Hin; fail). cbn in Hin, H.
  destruct (s_th σ u) as [[c [] i] |] eqn:E; try (destruct Hin; fail).
  destruct Hin as [<- | []]. injection H as <- <-. cbn. repeat split.
  - intros (thr & Hthr & Hs). rewrite E in Hthr. injection Hthr as <-. apply Hs. reflexivity.
  - eexists. cbn. unfold upd. destruct (Nat.eq_dec u u); [| congruence]. split; [reflexivity | discriminate].
  - exists c. reflexivity.
Qed.

(** An object stays an object of its class. *)
Lemma oprun_objects (t : tid) (nxt : nat) (X : Type) (o : op X) (σ σ' : state) (x : X) (r : nat) cls fs :
  oprun t nxt o σ = Did x σ' -> s_obj σ r = Some (cls, fs) -> exists fs', s_obj σ' r = Some (cls, fs').
Proof.
  intros H Hr. destruct o; cbn in H; unfold waiting, clear_intr in H; crack H; cbn;
    try (exists fs; exact Hr);
    try (unfold upd; match goal with |- context [Nat.eq_dec r ?k] => destruct (Nat.eq_dec r k) as [-> |] end;
         [| exists fs; exact Hr]).
  all: try congruence.
  all: try (eexists; f_equal; f_equal; congruence).
Qed.

Section Kept.

  Variable T : table.
  Variable known : classes.
  Variable named : string -> list val -> option program.

  (** ** Configurations *)

  (** The threads, the state, the references known, and a number no thread and no object has. *)
  Record cfg := Cfg { ths : list thread; heap : state; refs : list (Z * val); next : nat }.

  (** A step, at the moment `w`, of the thread at the place `n`. *)
  Inductive move (w : Z) (n : nat) (c : cfg) (act : action) (c' : cfg) : Prop :=
    | moved t top p under th' new :
        nth_error (ths c) n = Some (Active t top p under) ->
        shape T known named w (next c) (heap c) t top p under act th' (heap c') new ->
        refs c' = extend (refs c) (mentions act) -> placed_in (heap c') (mentions act) = true ->
        ths c' = firstn n (ths c) ++ th' :: skipn (S n) (ths c) ++ new -> next c' = S (next c) ->
        move w n c act c'.

  (** Steps one after another from the moment `w`: who stepped and what it did, and the configurations gone
      through, the first and the last among them. *)
  Inductive trace : Z -> cfg -> list (nat * action) -> list cfg -> Prop :=
    | trace_end w c : trace w c [] [c]
    | trace_step w c n act c1 log cs :
        move w n c act c1 -> trace (w + 1) c1 log cs -> trace w c ((n, act) :: log) (c :: cs).

  (** ** What is kept *)

  (** The calls under one made at `above`: each made before the one over it. *)
  Fixpoint descending (above : Z) (under : list (call * (res -> program))) : Prop :=
    match under with
    | [] => True
    | (c, _) :: rest => made c < above /\ descending (made c) rest
    end.

  Definition stacked (w : Z) (th : thread) : Prop :=
    match th with
    | Active _ top _ under => made top < w /\ descending (made top) under
    | Done _ _ => True
    end.

  Record inv (w : Z) (c : cfg) : Prop := Inv {
    inv_now : 0 <= w;
    inv_stacks : forall th, In th (ths c) -> stacked w th;
    inv_tids : NoDup (map tid_of (ths c));
    inv_started : forall th, In th (ths c) -> was_started (heap c) (tid_of th);
    inv_good : good (refs c);
    inv_placed : forall k cls r, In (k, vref cls r) (refs c) -> exists fs, s_obj (heap c) r = Some (cls, fs) }.

  Lemma stacked_later (w w' : Z) (th : thread) : w <= w' -> stacked w th -> stacked w' th.
  Proof. destruct th; cbn; [| auto]. intros Hw [H1 H2]. split; [lia | exact H2]. Qed.

  (** The thread a step leaves is the same thread, its calls in order. *)
  Lemma shape_thread w nxt σ t top p under act th' σ' new :
    shape T known named w nxt σ t top p under act th' σ' new -> stacked w (Active t top p under) ->
    tid_of th' = t /\ stacked (w + 1) th' /\ actor act = t /\ within act = made top.
  Proof.
    intros H [Htop Hunder]. destruct H as [x Hs Hans | kd m shown act' lp k Hc Hag | X o k x σ1 Hs Hsaid Hop Hok].
    - destruct under as [| [c k] rest]; cbn; [auto |]. destruct Hunder as [Hc Hrest].
      repeat split; try reflexivity; [lia | exact Hrest].
    - cbn. repeat split; try reflexivity; try lia; assumption.
    - cbn. repeat split; try reflexivity; try lia; assumption.
  Qed.

  (** What a step leaves of the threads and the objects. *)
  Lemma shape_state w nxt σ t top p under act th' σ' new :
    shape T known named w nxt σ t top p under act th' σ' new ->
    (forall u, was_started σ u -> was_started σ' u) /\
    (forall r cls fs, s_obj σ r = Some (cls, fs) -> exists fs', s_obj σ' r = Some (cls, fs')) /\
    (forall th, In th new ->
       ~ was_started σ (tid_of th) /\ was_started σ' (tid_of th) /\ exists c, th = root (tid_of th) c).
  Proof.
    intros H. destruct H as [x Hs Hans | kd m shown act' lp k Hc Hag | X o k x σ1 Hs Hsaid Hop Hok].
    - split; [| split; [| intros th []]].
      + destruct under; [intros u; apply started_terminate | auto].
      + intros r cls fs Hr. exists fs. destruct under; [rewrite objects_terminate |]; exact Hr.
    - split; [auto | split; [eauto | intros th []]].
    - split; [intros u; exact (oprun_started _ _ _ _ _ _ _ u Hop) | split].
      + intros r cls fs. exact (oprun_objects _ _ _ _ _ _ _ r cls fs Hop).
      + intros th. exact (started_fresh _ _ _ _ _ _ _ th Hop).
  Qed.

  Lemma in_extended (rs : list (Z * val)) (vs : list val) (k : Z) (v : val) :
    In (k, v) (extend rs vs) -> In (k, v) rs \/ In v vs.
  Proof.
    revert rs. induction vs as [| u rest IH]; intros rs H; [left; exact H |]. cbn in H.
    destruct (IH _ H) as [Hin | Hin]; [| right; right; exact Hin].
    destruct (referred u && negb (existsb (fun kv => val_eqb (snd kv) u) rs))%bool; [| left; exact Hin].
    apply in_app_or in Hin as [Hin | [E | []]]; [left; exact Hin | right; left; congruence].
  Qed.

  Lemma placed_object (σ : state) (vs : list val) (cls : string) (r : nat) :
    placed_in σ vs = true -> In (vref cls r) vs -> exists fs, s_obj σ r = Some (cls, fs).
  Proof.
    intros H Hin. unfold placed_in in H. rewrite forallb_forall in H. specialize (H _ Hin). cbn in H.
    destruct (s_obj σ r) as [[c fs] |]; [| discriminate]. apply String.eqb_eq in H. subst c. eauto.
  Qed.

  Lemma map_replaced (xs new : list thread) (n : nat) (old y : thread) :
    nth_error xs n = Some old -> tid_of y = tid_of old ->
    map tid_of (firstn n xs ++ y :: skipn (S n) xs ++ new) = map tid_of xs ++ map tid_of new.
  Proof.
    intros H Hy. rewrite (split_nth xs n old H) at 3.
    rewrite !map_app. cbn [map]. rewrite !map_app, Hy, <- app_assoc. reflexivity.
  Qed.

  Lemma inv_move (w : Z) (n : nat) (c c' : cfg) (act : action) : inv w c -> move w n c act c' -> inv (w + 1) c'.
  Proof.
    intros [Hw Hst Htids Hstarted Hgood Hplaced] [t top p under th' new Hn Hshape Hrefs Hp Hths Hnext].
    assert (In (Active t top p under) (ths c)) as Hin by (eapply nth_error_In; exact Hn).
    destruct (shape_thread _ _ _ _ _ _ _ _ _ _ _ Hshape (Hst _ Hin)) as (Htid & Hstacked & _).
    destruct (shape_state _ _ _ _ _ _ _ _ _ _ _ Hshape) as (Hkeep & Hobj & Hnew).
    split.
    - lia.
    - intros th Hth. rewrite Hths in Hth. apply in_replaced in Hth as [-> | [Hth | Hth]].
      + exact Hstacked.
      + apply (stacked_later w); [lia | exact (Hst _ Hth)].
      + destruct (Hnew _ Hth) as (_ & _ & cd & ->). cbn. split; [lia | exact I].
    - rewrite Hths, (map_replaced _ _ _ _ _ Hn Htid).
      assert (NoDup (map tid_of new) /\ forall u, In u (map tid_of new) -> ~ In u (map tid_of (ths c))) as [Hd Hfresh].
      { assert (new = [] \/ exists u cd i, new = [root u cd] /\ s_th (heap c) u = Some (Thread cd TNew i)) as Hone.
        { clear Hths Hnew. destruct Hshape; try (left; reflexivity). apply started_one. }
        destruct Hone as [-> | (u & cd & i & -> & E)]; [split; [constructor | intros u0 []] |].
        split; [repeat constructor; intros [] |]. intros u0 [<- | []] Hu.
        apply in_map_iff in Hu as (th & Hth & Hin'). destruct (Hstarted _ Hin') as (thr & Hthr & Hs).
        cbn in Hth. rewrite Hth, E in Hthr. injection Hthr as <-. apply Hs. reflexivity. }
      apply NoDup_app; [exact Htids | exact Hd |]. intros u Hu Hu'. exact (Hfresh u Hu' Hu).
    - intros th Hth. rewrite Hths in Hth. apply in_replaced in Hth as [-> | [Hth | Hth]].
      + rewrite Htid. apply Hkeep. exact (Hstarted _ Hin).
      + apply Hkeep. exact (Hstarted _ Hth).
      + apply (Hnew _ Hth).
    - rewrite Hrefs. apply good_extend, Hgood.
    - intros k cls r Hk. rewrite Hrefs in Hk. apply in_extended in Hk as [Hk | Hk].
      + destruct (Hplaced _ _ _ Hk) as [fs Hfs]. exact (Hobj _ _ _ Hfs).
      + exact (placed_object _ _ _ _ Hp Hk).
  Qed.

End Kept.
