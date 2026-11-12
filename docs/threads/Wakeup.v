(** No lost wake-up in an Ox supervisor (`ox.DefaultSupervisor`, Ox 1.1.0), for docs/THREADS.md.

    A supervised scope's owner waits on a future (`result.get()`). A user fork is counted when it is started
    (`running.incrementAndGet()`); when its body succeeds it takes itself off the count and, if it read zero,
    completes the future (`if running.decrementAndGet() == 0 then result.complete(Success)`), two steps with any
    other thread's steps between them; when its body fails it completes the future at once.

    A wake-up is lost when the owner waits, what it waits for has come about, and nobody will tell it. The model
    has the count, the future, each user fork (not started, in its body, between its decrement and its
    completing, finished, failed) and the owner (arriving at the wait, parked, woken).

    What is assumed of the JDK is in the steps: `incrementAndGet` and `decrementAndGet` are each one step, and
    the future latches (`latching`): a `complete` made before the owner waits is still there when it does. The
    second theorem drops that assumption: a signal that reaches only an owner already parked can be lost.

    Plain Rocq with its standard library, no axioms: `rocq compile docs/threads/Wakeup.v`. *)

From Stdlib Require Import Arith Lia.

Inductive fstatus := NotStarted | InBody | Dec (v : nat) | Finished | Failed.
Inductive opc := Arriving | Parked | Woken.

Record state := State {
  status : nat -> fstatus;   (* each user fork *)
  running : nat;             (* the supervisor's count *)
  done : bool;               (* the future is completed *)
  owner : opc }.

Definition upd {B : Type} (f : nat -> B) (k : nat) (v : B) : nat -> B :=
  fun x => if Nat.eq_dec x k then v else f x.

Definition init := State (fun _ => NotStarted) 0 false Arriving.

Fixpoint sum (n : nat) (f : nat -> nat) : nat :=
  match n with 0 => 0 | S k => f k + sum k f end.

Lemma sum_ext n f g : (forall u, u < n -> f u = g u) -> sum n f = sum n g.
Proof.
  induction n as [| n IH]; intro H; cbn; trivial.
  rewrite (H n), IH; auto.
Qed.

Lemma sum_zero n f : (forall u, u < n -> f u = 0) -> sum n f = 0.
Proof.
  induction n as [| n IH]; intro H; cbn; trivial.
  rewrite (H n), IH; auto.
Qed.

Lemma sum_upd n f t v : t < n -> sum n (upd f t v) + f t = sum n f + v.
Proof.
  induction n as [| n IH]; intro Ht; [lia |]. cbn.
  destruct (Nat.eq_dec t n) as [-> | Hne].
  - rewrite (sum_ext n (upd f n v) f).
    + unfold upd. destruct (Nat.eq_dec n n); [lia | contradiction].
    + intros u Hu. unfold upd. destruct (Nat.eq_dec u n); [lia | reflexivity].
  - assert (He : upd f t v n = f n) by (unfold upd; destruct (Nat.eq_dec n t); [congruence | reflexivity]).
    rewrite He. assert (Hlt : t < n) by lia. specialize (IH Hlt). lia.
Qed.

Section Supervisor.

Variable N : nat.            (* user forks are numbered below N *)
Variable latching : Prop.    (* a completion made before the owner waits is kept *)

Inductive step : state -> state -> Prop :=
  | spawn s t : t < N -> status s t = NotStarted ->
      step s (State (upd (status s) t InBody) (S (running s)) (done s) (owner s))
  | decrement s t : t < N -> status s t = InBody ->
      step s (State (upd (status s) t (Dec (pred (running s)))) (pred (running s)) (done s) (owner s))
  | signal s t v : t < N -> status s t = Dec v ->
      step s (State (upd (status s) t Finished) (running s) (if Nat.eqb v 0 then true else done s) (owner s))
  | signal_lost s t : ~ latching -> t < N -> status s t = Dec 0 -> owner s = Arriving ->
      step s (State (upd (status s) t Finished) (running s) (done s) (owner s))
  | fail s t : t < N -> status s t = InBody ->
      step s (State (upd (status s) t Failed) (running s) true (owner s))
  | park s : owner s = Arriving -> done s = false ->
      step s (State (status s) (running s) (done s) Parked)
  | pass s : owner s = Arriving -> done s = true ->
      step s (State (status s) (running s) (done s) Woken)
  | wake s : owner s = Parked -> done s = true ->
      step s (State (status s) (running s) (done s) Woken).

Inductive reachable : state -> Prop :=
  | r_init : reachable init
  | r_step s s' : reachable s -> step s s' -> reachable s'.

(** A fork is on the count from its start until its decrement; a failed fork stays on it. *)
Definition counted (x : fstatus) : nat :=
  match x with InBody | Failed => 1 | _ => 0 end.

Definition count (st : nat -> fstatus) : nat := sum N (fun t => counted (st t)).

Lemma count_upd st t x : t < N -> count (upd st t x) + counted (st t) = count st + counted x.
Proof.
  intro Ht. unfold count.
  rewrite (sum_ext N (fun u => counted (upd st t x u)) (upd (fun u => counted (st u)) t (counted x))).
  - apply (sum_upd N (fun u => counted (st u)) t (counted x) Ht).
  - intros u _. unfold upd. destruct (Nat.eq_dec u t); reflexivity.
Qed.

(** What every step keeps, when the future latches: the count is the forks on it; a failure has completed the
    future; and while the future is not completed and the count is zero, either no fork was started or one is
    between its decrement to zero and its completing the future. *)
Definition inv (s : state) : Prop :=
  running s = count (status s) /\
  (forall t, t < N -> status s t = Failed -> done s = true) /\
  (done s = false -> running s = 0 ->
     (forall t, t < N -> status s t = NotStarted) \/ exists t, t < N /\ status s t = Dec 0).

Lemma inv_init : inv init.
Proof.
  repeat split; cbn; intros; try discriminate.
  - unfold count. symmetry. apply sum_zero. reflexivity.
  - left. reflexivity.
Qed.

Lemma inv_step s s' : latching -> inv s -> step s s' -> inv s'.
Proof.
  intros Hl (HA & HC & HB) Hstep.
  destruct Hstep as [s t Ht Hs | s t Ht Hs | s t v Ht Hs | s t Hn | s t Ht Hs | s Ho Hd | s Ho Hd | s Ho Hd];
    try contradiction; unfold inv; cbn.
  - (* spawn *)
    pose proof (count_upd (status s) t InBody Ht) as Hc. rewrite Hs in Hc; cbn in Hc.
    split; [lia | split; [| intros _ H; discriminate]].
    intros u Hu. unfold upd. destruct (Nat.eq_dec u t); [discriminate | apply HC, Hu].
  - (* decrement *)
    pose proof (count_upd (status s) t (Dec (pred (running s))) Ht) as Hc. rewrite Hs in Hc; cbn in Hc.
    split; [lia | split].
    + intros u Hu. unfold upd. destruct (Nat.eq_dec u t); [discriminate | apply HC, Hu].
    + intros _ Hz. right. exists t. split; trivial.
      unfold upd. destruct (Nat.eq_dec t t); [rewrite Hz; reflexivity | contradiction].
  - (* signal *)
    pose proof (count_upd (status s) t Finished Ht) as Hc. rewrite Hs in Hc; cbn in Hc.
    split; [lia | split].
    + intros u Hu. unfold upd. destruct (Nat.eq_dec u t); [discriminate |].
      intro Hf. rewrite (HC u Hu Hf). destruct (Nat.eqb v 0); reflexivity.
    + destruct (Nat.eqb_spec v 0) as [Hv | Hv]; [discriminate |].
      intros Hd Hz. destruct (HB Hd Hz) as [Hall | [u [Hu Hdec]]].
      * rewrite (Hall t Ht) in Hs. discriminate.
      * right. exists u. split; trivial.
        unfold upd. destruct (Nat.eq_dec u t) as [-> |]; [| exact Hdec].
        rewrite Hs in Hdec. injection Hdec as Hv0. contradiction.
  - (* fail *)
    pose proof (count_upd (status s) t Failed Ht) as Hc. rewrite Hs in Hc; cbn in Hc.
    split; [lia | split; [intros; reflexivity | intro H; discriminate]].
  - repeat split; assumption.
  - repeat split; assumption.
  - repeat split; assumption.
Qed.

Lemma inv_reachable s : latching -> reachable s -> inv s.
Proof. intros Hl Hr. induction Hr; [apply inv_init | eapply inv_step; eassumption]. Qed.

(** No lost wake-up. When the future latches: once a user fork has been started and none is in its body, the
    future is completed, or a fork is between its decrement to zero and its completing the future. *)
Theorem no_lost_wakeup s : latching -> reachable s ->
  (exists t, t < N /\ status s t <> NotStarted) ->
  (forall t, t < N -> status s t <> InBody) ->
  done s = true \/ exists t, t < N /\ status s t = Dec 0.
Proof.
  intros Hl Hr [t0 [Ht0 Hst]] Hnone.
  destruct (inv_reachable s Hl Hr) as (HA & HC & HB).
  destruct (done s) eqn:Hd; [left; reflexivity | right].
  assert (Hz : running s = 0).
  { rewrite HA. apply sum_zero. intros u Hu.
    specialize (Hnone u Hu). specialize (HC u Hu).
    destruct (status s u); cbn; trivial; [contradiction | discriminate (HC eq_refl)]. }
  destruct (HB eq_refl Hz) as [Hall | Hex]; [| exact Hex].
  elim Hst. apply Hall, Ht0.
Qed.

(** A completed future stays completed, so a wake-up that is on offer stays on offer until the owner takes it. *)
Theorem done_stays s s' : latching -> step s s' -> done s = true -> done s' = true.
Proof.
  intros Hl Hstep Hd. destruct Hstep; cbn; trivial; try contradiction.
  rewrite Hd. destruct (Nat.eqb v 0); reflexivity.
Qed.

(** Without latching the wake-up can be lost: the one fork decrements to zero and signals while the owner is
    still arriving, the signal reaches nobody, and the owner then parks. The fork has finished, the future is not
    completed, and no fork is left to complete it. *)
Theorem lost_without_latching : ~ latching -> 0 < N -> exists s,
  reachable s /\ owner s = Parked /\ done s = false /\ status s 0 = Finished /\
  forall t, t < N -> status s t = Finished \/ status s t = NotStarted.
Proof.
  intros Hn HN.
  eexists. split; [| split; [| split; [| split]]].
  - eapply r_step; [eapply r_step; [eapply r_step; [eapply r_step; [apply r_init |] |] |] |].
    + apply (spawn init 0); trivial.
    + apply (decrement _ 0); trivial.
    + apply (signal_lost _ 0); trivial.
    + apply park; trivial.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t _. cbn. unfold upd. destruct (Nat.eq_dec t 0); auto.
Qed.

End Supervisor.
