(** Liveness of an Ox scope's closing loop (`ThreadHerd.interruptAllAndJoinUntilCompleted`, Ox 1.1.0), for
    docs/THREADS.md: under a fair scheduler, a scope that is closing completes.

    The model is the closing phase alone. The forks are those in the set when the scope starts to close, numbered
    below `N`. The owner interrupts each fork once and leaves when none is left. A fork not yet interrupted may
    run for ever (`spin`) or end; a fork interrupted takes at most `fuel` more steps of its body and ends.

    What is assumed, beside what `Herd.v` assumes:
    - of each fork's body: once interrupted it ends within a bound (`fuel`), and it starts no fork;
    - of `Thread.interrupt`: the request reaches the fork, also one made before the fork's first step;
    - of the scheduler (`fair`): an actor that could step at every moment from some moment on, does step.

    A run is an infinite sequence of states, so "eventually" is `exists n`. The proof is a rank that no step
    raises and every step but `spin` lowers; fairness of the owner is what ends the spinning. Plain Rocq with its
    standard library and excluded middle (`classic`): `rocq compile docs/threads/Closing.v`. *)

From Stdlib Require Import Arith Lia Classical.

Record state := State {
  live : nat -> bool;      (* the fork is in the set, running its body *)
  intr : nat -> bool;      (* the owner has interrupted it *)
  fuel : nat -> nat;       (* the steps its body may still take once interrupted *)
  exited : bool }.         (* the owner is past the loop *)

Inductive actor := Owner | Fork (t : nat).

Definition upd {B : Type} (f : nat -> B) (k : nat) (v : B) : nat -> B :=
  fun x => if Nat.eq_dec x k then v else f x.

Section Loop.

Variable N : nat.

Inductive step : actor -> state -> state -> Prop :=
  | interrupt s t : t < N -> exited s = false -> live s t = true -> intr s t = false ->
      step Owner s (State (live s) (upd (intr s) t true) (fuel s) (exited s))
  | leave s : exited s = false -> (forall t, t < N -> live s t = false) ->
      step Owner s (State (live s) (intr s) (fuel s) true)
  | spin s t : t < N -> live s t = true -> intr s t = false ->
      step (Fork t) s s
  | work s t k : t < N -> live s t = true -> intr s t = true -> fuel s t = S k ->
      step (Fork t) s (State (live s) (intr s) (upd (fuel s) t k) (exited s))
  | finish s t : t < N -> live s t = true ->
      step (Fork t) s (State (upd (live s) t false) (intr s) (fuel s) (exited s)).

(** A run: each state follows the one before by a step, or nothing can step and it stays. *)
Definition run_ok (r : nat -> state) : Prop :=
  forall n, (exists a, step a (r n) (r (S n))) \/ ((forall a s', ~ step a (r n) s') /\ r (S n) = r n).

Definition enabled (a : actor) (s : state) : Prop := exists s', step a s s'.

(** Weak fairness, of the owner and of each fork. *)
Definition fair (r : nat -> state) : Prop :=
  forall a n, (forall m, n <= m -> enabled a (r m)) -> exists m, n <= m /\ step a (r m) (r (S m)).

(** The rank: one for the owner's leaving, and for each fork in the set its fuel, one for its ending, and one
    more while it is not interrupted. *)
Definition weight (s : state) (t : nat) : nat :=
  if live s t then (if intr s t then 1 + fuel s t else 2 + fuel s t) else 0.

Fixpoint sum (n : nat) (f : nat -> nat) : nat :=
  match n with 0 => 0 | S k => f k + sum k f end.

Definition rank (s : state) : nat := (if exited s then 0 else 1) + sum N (weight s).

Lemma sum_ext n f g : (forall u, u < n -> f u = g u) -> sum n f = sum n g.
Proof.
  induction n as [| n IH]; intro H; cbn; trivial.
  rewrite (H n), IH; auto.
Qed.

Lemma sum_lt n f g t : t < n -> (forall u, u < n -> u <> t -> f u = g u) -> f t < g t -> sum n f < sum n g.
Proof.
  induction n as [| n IH]; intros Ht H Hlt; [lia |]. cbn.
  destruct (Nat.eq_dec t n) as [-> | Hne].
  - rewrite (sum_ext n f g); [lia |]. intros u Hu. apply H; lia.
  - rewrite (H n) by lia. apply Nat.add_lt_mono_l. apply IH; [lia | | exact Hlt]. intros; apply H; lia.
Qed.

(** Every step lowers the rank, but a fork's spinning before it is interrupted, which changes nothing. *)
Lemma step_rank a s s' : step a s s' ->
  rank s' < rank s \/ (s' = s /\ exists t, a = Fork t /\ t < N /\ live s t = true /\ intr s t = false).
Proof.
  intro H. destruct H as [s t Ht He Hl Hi | s He Hall | s t Ht Hl Hi | s t k Ht Hl Hi Hf | s t Ht Hl].
  - left. unfold rank; cbn. apply Nat.add_lt_mono_l. apply (sum_lt N _ _ t Ht).
    + intros u _ Hu. unfold weight, upd; cbn. destruct (Nat.eq_dec u t); [contradiction | reflexivity].
    + unfold weight, upd; cbn. rewrite Hl, Hi. destruct (Nat.eq_dec t t); [lia | contradiction].
  - left. unfold rank; cbn. rewrite He. apply Nat.lt_succ_diag_r.
  - right. split; trivial. exists t. auto.
  - left. unfold rank; cbn. apply Nat.add_lt_mono_l. apply (sum_lt N _ _ t Ht).
    + intros u _ Hu. unfold weight, upd; cbn. destruct (Nat.eq_dec u t); [contradiction | reflexivity].
    + unfold weight, upd; cbn. rewrite Hl, Hi, Hf. destruct (Nat.eq_dec t t); [lia | contradiction].
  - left. unfold rank; cbn. apply Nat.add_lt_mono_l. apply (sum_lt N _ _ t Ht).
    + intros u _ Hu. unfold weight, upd; cbn. destruct (Nat.eq_dec u t); [contradiction | reflexivity].
    + unfold weight, upd; cbn. rewrite Hl. destruct (Nat.eq_dec t t); [| contradiction].
      destruct (intr s t); lia.
Qed.

(** Until the owner has left, something can step. *)
Lemma progress s : exited s = false -> exists a s', step a s s'.
Proof.
  intro He. destruct (classic (exists t, t < N /\ live s t = true)) as [[t [Ht Hl]] | Hnone].
  - exists (Fork t). eexists. apply finish; assumption.
  - exists Owner. eexists. apply leave; trivial.
    intros t Ht. destruct (live s t) eqn:E; trivial. elim Hnone. exists t. auto.
Qed.

(** Until the owner has left, a fair run reaches a state of lower rank. *)
Lemma rank_falls r i : run_ok r -> fair r -> exited (r i) = false -> exists j, rank (r j) < rank (r i).
Proof.
  intros Hrun Hfair He.
  apply NNPP. intro Hno.
  assert (Hge : forall j, rank (r i) <= rank (r j)).
  { intro j. destruct (Nat.le_gt_cases (rank (r i)) (rank (r j))); trivial. elim Hno. exists j. assumption. }
  assert (Hconst : forall d, r (i + d) = r i).
  { induction d as [| d IH]; [rewrite Nat.add_0_r; reflexivity |].
    rewrite Nat.add_succ_r. destruct (Hrun (i + d)) as [[a Hs] | [_ Heq]].
    - destruct (step_rank _ _ _ Hs) as [Hlt | [Heq _]].
      + rewrite IH in Hlt. specialize (Hge (S (i + d))). lia.
      + rewrite Heq. exact IH.
    - rewrite Heq. exact IH. }
  assert (Hat : forall m, i <= m -> r m = r i).
  { intros m Hm. replace m with (i + (m - i)) by lia. apply Hconst. }
  assert (Hself : forall a, enabled a (r i) -> step a (r i) (r i)).
  { intros a Hen. destruct (Hfair a i) as [m [Hm Hs]].
    - intros m Hm. rewrite (Hat m Hm). exact Hen.
    - rewrite (Hat m Hm), (Hat (S m)) in Hs by lia. exact Hs. }
  destruct (progress (r i) He) as [a [s' Hs]].
  destruct (step_rank _ _ _ (Hself a (ex_intro _ s' Hs))) as [Hlt | [_ [t [_ [Ht [Hl Hi]]]]]]; [lia |].
  assert (Hown : enabled Owner (r i)) by (eexists; apply (interrupt (r i) t); assumption).
  destruct (step_rank _ _ _ (Hself Owner Hown)) as [Hlt | [_ [u [Hu _]]]]; [lia | discriminate].
Qed.

(** A closing scope completes: in every fair run the owner gets past the loop. *)
Theorem closes r : run_ok r -> fair r -> exists n, exited (r n) = true.
Proof.
  intros Hrun Hfair.
  assert (H : forall k i, rank (r i) = k -> exists n, exited (r n) = true).
  { induction k as [k IH] using lt_wf_ind. intros i Hk.
    destruct (exited (r i)) eqn:He; [exists i; exact He |].
    destruct (rank_falls r i Hrun Hfair He) as [j Hj].
    apply (IH (rank (r j))) with (i := j); [lia | reflexivity]. }
  apply (H (rank (r 0)) 0). reflexivity.
Qed.

(** Fairness is needed: with one fork, the run in which that fork spins for ever is a run, and the owner never
    leaves. It is unfair to the owner alone, whose interrupt could be made at every moment. *)
Theorem needs_fairness : 0 < N -> exists r, run_ok r /\ forall n, exited (r n) = false.
Proof.
  intro HN.
  exists (fun _ => State (fun _ => true) (fun _ => false) (fun _ => 0) false).
  split; [| reflexivity].
  intro n. left. exists (Fork 0). apply spin; trivial.
Qed.

End Loop.
