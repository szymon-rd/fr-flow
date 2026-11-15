Require Export FrFlowGen.OxThreads.closingSetsTheFlagItself.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree: it first calls `assertOnOwnerThread`, which
    returns where the caller is the herd's owner; then it sets the flag; whatever it does after, it completes
    only then. *)
Lemma closingSetsTheFlagItself_Proofs_complete : closingSetsTheFlagItself_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hfields Hcurrent h from response to Hdone.
  pose proof (completed_was_called _ _ _ _ _ _ Hdone) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled)
    as (r & inside & Hh & Hcall).
  destruct Hdone as [[(ins & spawns & Hat) _] | [_ [spawns Hend]]]; [rewrite Hcall in Hat; discriminate Hat |].
  assert (forall k, direct (heldIn "ox.internal.ThreadHerd herdOwner" h) from (history k) ->
    forall resp sp, history k = Event_Respond (heldIn "ox.internal.ThreadHerd herdOwner" h) from resp sp ->
    exists a response_1 b, (from <= a /\ b <= k) /\ exists who, completedBy history
      (Invocation_mk "java.util.concurrent.atomic.AtomicBoolean set scala.Boolean:scala.Unit"
        [heldIn "ox.internal.ThreadHerd shutdownInProgress" h; Value_Bool_ True]) who a response_1 b) as Hall.
  { refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
      Hcall Hh eq_refl _).
    intros args k Hargs _. apply vals_none in Hargs as ->.
    (* assertOnOwnerThread is called: it returns, the caller being the herd's owner *)
    step. intros w1 ys Hw1 _ Hys Hinv. split; [miss |]. intros w2 rr sp x Hw2 Hresp Hgives.
    apply args_one in Hys as (y0 & -> & Hy0). pose proof (one_name N _ _ _ Hy0 Hh) as ->.
    destruct x as [e | v].
    { exfalso. destruct rr as [y | y]; [contradiction |].
      exact (assertOnOwnerThread_returns C (proj2 (proj1 (proj1 (Hfields h)))) Hcurrent Hh Hinv w2
        ltac:(rewrite Hresp; cbn; auto) y sp Hresp). }
    (* the flag is read *)
    step. intros wr vf y Hwr _ Hy Hty Hread. split; [miss |]. apply (proj2 (proj1 (Hfields h))) in Hread. subst y.
    (* and set: whatever the call does after, it has set the flag *)
    step. intros ws yss Hws _ Hyss Hmk. split; [miss |]. intros wd a x Hwd Hset _ _.
    apply args_two in Hyss as (y1 & y2 & -> & Hy1 & Hy2).
    rewrite (one_name N _ _ _ Hy1 Hy) in Hset. apply named_bool in Hy2. subst y2.
    apply meets_from. intros k' Hk' resp sp' _. exists ws, a, wd. split; [lia |]. eexists.
    exact (done_completed Hset). }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) response spawns Hend) as (a & r1 & b & [Ha Hb] & Hd).
  exists a, r1, b. split; [lia | exact Hd].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma closingSetsTheFlagItself_Proofs_feasible : closingSetsTheFlagItself_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H). }
  split.
  { intros h. repeat split; intros w by_ inside found H; discriminate H. }
  intros c from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
