Require Export FrFlowGen.OxThreads.closingSetsTheFlagItself.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree: it first calls `assertOnOwnerThread`, which
    returns where the caller is the herd's owner; then it sets the flag; whatever it does after, it completes
    only then. *)
Lemma closingSetsTheFlagItself_Proofs_complete : closingSetsTheFlagItself_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hfields Hcurrent h from response to Hdone.
  assert (exists r, names N h (vref "ox.internal.ThreadHerd" r)) as [r Hh].
  { destruct (Hmade h h from) as (m & b & ins & hs & _ & Hmk); [| exact (made_named C Hmk)].
    right. eexists. exact (completed_was_called _ _ _ _ _ _ Hdone). }
  destruct Hdone as [[(inside & spawns & Hat) _] | [[inside Hcall] [spawns Hend]]].
  { exfalso. exact (method_not_atomic C
      (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") Hat Hh eq_refl). }
  destruct (method_steps C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl) as (args & at_ & Hargs & _ & Hlater & Hsteps & Htakes).
  inversion Hargs; subst. clear Hargs.
  assert (direct (heldIn "ox.internal.ThreadHerd herdOwner" h) from (history (to - 1))) as Hdirect
    by (rewrite Hend; cbn; auto).
  pose proof (Hlater _ Hdirect) as Hw.
  pose proof (Htakes _ Hw (or_introl Hdirect)) as Hgo. rewrite Hend in Hgo.
  pose proof (Hsteps _ Hw) as H. clear Hsteps Htakes Hlater.
  revert Hgo. generalize (at_ (to - 1 + 1)). revert H. generalize (at_ (to - 1)). intros st H st' Hgo.
  walk H.
  apply step_method in H as [[-> _] | (w1 & ys & Hw1 & _ & Hys & Hinv & Hnext)].
  { exfalso. refine (respond_call _ Hgo). exact I. }
  destruct Hnext as [(-> & _) | (w2 & r' & sp & x & Hw2 & _ & _ & Hresp & Hgives & H)].
  { exfalso. pose proof (respond_waiting Hgo). lia. }
  cbn in Hys. inversion Hys as [| y0 v0 ys0 vs0 Hy0 Hrest]; subst. inversion Hrest; subst.
  (* assertOnOwnerThread returns: the thread that calls is the herd's owner *)
  assert (x = inr VUnit) as ->.
  { destruct (method_steps C (Member "ox.internal.ThreadHerd" "assertOnOwnerThread" ":scala.Unit") Hinv Hy0
      eq_refl) as (args2 & at2 & Hargs2 & _ & _ & Hsteps2 & Htakes2).
    inversion Hargs2; subst.
    pose proof (Hsteps2 w2 ltac:(lia)) as H2.
    assert (takes Code_table N (heldIn "ox.internal.ThreadHerd herdOwner" h) w1 w2
      (Event_Respond (heldIn "ox.internal.ThreadHerd herdOwner" h) w1 r' sp) (at2 w2) (at2 (w2 + 1))) as Hgo2.
    { rewrite <- Hresp. apply Htakes2; [lia |]. left. rewrite Hresp. cbn. auto. }
    revert Hgo2. generalize (at2 (w2 + 1)). revert H2. generalize (at2 w2). clear Hsteps2 Htakes2.
    intros st2 H2 st2' Hgo2.
    (* Thread.currentThread() *)
    walk H2.
    apply step_called in H2 as [[-> _] | (w3 & ys3 & Hw3 & _ & Hys3 & [(_ & -> & _) |
      (w4 & a & xc & Hw4 & _ & Hcur & Hgc & Htc & H2)])].
    { exfalso. refine (respond_vis _ Hgo2). intros []. }
    { exfalso. pose proof (respond_waiting Hgo2). lia. }
    inversion Hys3; subst.
    assert (a = Response_Returned (heldIn "ox.internal.ThreadHerd herdOwner" h)) as ->.
    { apply (Hcurrent _ w3 a w4). unfold completedBy, doneAtOnce, begun.
      destruct Hcur as [(sp' & Hat' & ->) | (Hinv' & _ & sp' & Hresp')]; [left | right]; eauto. }
    destruct xc as [e | current]; [contradiction |].
    change (names N (heldIn "ox.internal.ThreadHerd herdOwner" h) current) in Hgc.
    change (identity current) in Htc.
    (* the herd's owner, read *)
    walk H2.
    apply step_read in H2 as [[-> _] | (w5 & v & y & yo & Hw5 & _ & Hyo & Hy & Hty & Hread & H2)].
    { exfalso. refine (respond_vis _ Hgo2). intros []. }
    destruct (read_place Hh Hyo) as [-> Hcls]. rewrite Hcls in Hty, Hread.
    apply (proj2 (Hfields h)) in Hread. subst y.
    pose proof (names_one N _ _ _ Hy Hgc) as ->.
    (* they are the same thread: nothing is thrown *)
    walk H2.
    exact (gives_one Hgives (ends_with H2 Hgo2)). }
  (* the flag, read *)
  walk H.
  apply step_read in H as [[-> _] | (w3 & v & y & yo & Hw3 & _ & Hyo & Hy & Hty & Hread & H)].
  { exfalso. refine (respond_vis _ Hgo). intros []. }
  destruct (read_place Hh Hyo) as [-> Hcls]. rewrite Hcls in Hty, Hread.
  apply (proj1 (proj1 (Hfields h))) in Hread. subst y.
  apply identity_receiver in Hty.
  (* and set *)
  walk H.
  apply step_called in H as [[-> _] | (w4 & ys4 & Hw4 & _ & Hys4 & [(_ & -> & _) |
    (w5 & a & xs & Hw5 & _ & Hset & _)])].
  { exfalso. refine (respond_vis _ Hgo). intros []. }
  { exfalso. pose proof (respond_waiting Hgo). lia. }
  inversion Hys4 as [| y1 v1 ys1 vs1 Hy1 Hrest1]; subst.
  inversion Hrest1 as [| y2 v2 ys2 vs2 Hy2 Hrest2]; subst. inversion Hrest2; subst.
  rewrite (one_name N _ _ _ Hy1 Hy) in Hset. apply named_bool in Hy2. subst y2.
  exists w4, a, w5. split; [lia |]. eexists. unfold completedBy, doneAtOnce, begun.
  destruct Hset as [(sp' & Hat' & ->) | (Hinv' & _ & sp' & Hresp')]; [left | right]; eauto.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma closingSetsTheFlagItself_Proofs_feasible : closingSetsTheFlagItself_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h code w [[who H] | [who H]]; destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h. repeat split; intros w by_ inside found H; discriminate H. }
  intros c from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
