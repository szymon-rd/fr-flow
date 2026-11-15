Require Export FrFlowGen.OxThreads.startThreadReadsTheFlagUnset.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk.

(** Proven of `ThreadHerd.startThread`'s tree: its first step is a call of `assertNotShuttingDown`, which reads
    the herd's flag and throws if it is set; what `startThread` does after is done only once that call has
    returned. *)
Lemma startThreadReadsTheFlagUnset_Proofs_complete : startThreadReadsTheFlagUnset_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hfields h code c t from w [Hcalled Hthen].
  assert (exists r, names N h (vref "ox.internal.ThreadHerd" r)) as [r Hh].
  { destruct (Hmade h code from) as (m & b & ins & hs & _ & Hmk); [| exact (made_named C Hmk)].
    left. exists c. exact Hcalled. }
  destruct Hcalled as [[inside Hcall] | (a & inside & spawns & Hat)].
  2: { exfalso. exact (method_not_atomic C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit")
         Hat Hh eq_refl). }
  destruct (method_steps C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh
    eq_refl) as (args & at_ & Hargs & _ & Hlater & Hsteps & Htakes).
  inversion Hargs as [| ycode vcode ys0 vs0 Hcode Hrest]; subst. inversion Hrest; subst. clear Hargs Hrest.
  (* where the call is at any moment: before its first step, waiting for it, past it having thrown, or the
     flag has been read as unset *)
  assert (forall k st, steps Code_table N history c from (from + 1)
      (Running (run Code_table (Method (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit"))
        (VList [vref "ox.internal.ThreadHerd" r; vcode]))) k st ->
    (exists K, st = Running (Call (Method (Member "ox.internal.ThreadHerd" "assertNotShuttingDown" ":scala.Unit"))
      (VList [vref "ox.internal.ThreadHerd" r]) K)) \/
    (exists w1 ty K, st = Waiting w1 ty K /\ from < w1) \/
    (exists e, st = Running (Ret (inl e))) \/ st = Ended \/
    (exists a b, (from <= a /\ b <= k) /\ exists who, completedBy history
      (Invocation_mk "java.util.concurrent.atomic.AtomicBoolean get :scala.Boolean"
        [heldIn "ox.internal.ThreadHerd shutdownInProgress" h]) who a (Response_Returned (Value_Bool_ False)) b))
    as Hwalk.
  { intros k st H. walk H.
    apply step_method in H as [[-> _] | (w1 & ys & Hw1 & _ & Hys & Hinv & Hnext)].
    { left. eexists. reflexivity. }
    destruct Hnext as [(-> & _) | (w2 & r' & sp & x & Hw2 & _ & _ & Hresp & Hgives & H)].
    { right; left. exists w1. eexists. eexists. split; [reflexivity | lia]. }
    (* the call of assertNotShuttingDown, made at w1 and responded to at w2 *)
    cbn in Hys. inversion Hys as [| y0 v0 ys0 vs0 Hy0 Hrest]; subst. inversion Hrest; subst.
    destruct (method_steps C (Member "ox.internal.ThreadHerd" "assertNotShuttingDown" ":scala.Unit") Hinv Hy0
      eq_refl) as (args2 & at2 & Hargs2 & _ & _ & Hsteps2 & Htakes2).
    inversion Hargs2; subst.
    pose proof (Hsteps2 w2 ltac:(lia)) as H2.
    assert (takes Code_table N c w1 w2 (Event_Respond c w1 r' sp) (at2 w2) (at2 (w2 + 1))) as Hgo2.
    { rewrite <- Hresp. apply Htakes2; [lia |]. left. rewrite Hresp. cbn. auto. }
    revert Hgo2. generalize (at2 (w2 + 1)). revert H2. generalize (at2 w2). clear Hsteps2 Htakes2.
    intros st2 H2 st2' Hgo2.
    walk H2. apply step_read in H2 as [[-> _] | (w3 & v & y & yo & Hw3 & _ & Hyo & Hy & Hty & Hread & H2)].
    { exfalso. refine (respond_vis _ Hgo2). intros []. }
    destruct (read_place Hh Hyo) as [-> Hcls]. rewrite Hcls in Hty, Hread.
    apply (proj1 (proj1 (Hfields h))) in Hread. subst y.
    apply identity_receiver in Hty.
    walk H2.
    apply step_called in H2 as [[-> _] | (w4 & ys & Hw4 & _ & Hys2 & [(_ & -> & _) |
      (w5 & a & xg & Hw5 & _ & Hget & Hgg & Htyped & H2)])].
    { exfalso. refine (respond_vis _ Hgo2). intros []. }
    { exfalso. pose proof (respond_waiting Hgo2). lia. }
    inversion Hys2 as [| y1 v1 ys1 vs1 Hy1 Hrest1]; subst. inversion Hrest1; subst.
    rewrite (one_name N _ _ _ Hy1 Hy) in Hget.
    destruct xg as [e | answer].
    { (* the read threw: so does assertNotShuttingDown, and so startThread *)
      walk H2. pose proof (gives_one Hgives (ends_with H2 Hgo2)) as ->. walk H.
      apply step_ret in H as [[-> _] | (w6 & r6 & _ & _ & _ & _ & -> & _)]; [right; right; left; eauto | auto]. }
    cbn in Htyped. destruct Htyped as [flag ->]. destruct flag.
    { (* the flag is set: assertNotShuttingDown throws, and so startThread *)
      walk H2. pose proof (gives_one Hgives (ends_with H2 Hgo2)) as ->. walk H.
      apply step_ret in H as [[-> _] | (w6 & r6 & _ & _ & _ & _ & -> & _)]; [right; right; left; eauto | auto]. }
    (* the flag is unset: this read is the one *)
    destruct a as [answer | thrown]; [| contradiction]. apply named_bool in Hgg. subst answer.
    right; right; right; right. exists w4, w5. split; [lia |]. exists c. unfold completedBy, doneAtOnce, begun.
    destruct Hget as [(sp' & Hat & ->) | (Hinv' & _ & sp' & Hresp')]; [left | right]; eauto. }
  destruct Hthen as [Hadd | [[(ins & sp & Hat) _] | [_ [sp Hend]]]].
  - (* the call itself adds a thread at w *)
    assert (direct c from (history w)) as Hdirect.
    { destruct Hadd as [E | (a & sp & E)]; rewrite E; cbn; auto. }
    pose proof (Hlater w Hdirect) as Hw.
    pose proof (Htakes w Hw (or_introl Hdirect)) as Hgo.
    destruct (Hwalk w _ (Hsteps w Hw)) as [[K E] | [(w1 & ty & K & E & Hw1) | [[e E] | [E | Hdone]]]];
      try (rewrite E in Hgo).
    + apply takes_method_call in Hgo as (ys & _ & He & _).
      destruct Hadd as [E' | (a & sp & E')]; rewrite E' in He; discriminate He.
    + apply takes_waiting in Hgo as (r' & sp & x & He & _).
      destruct Hadd as [E' | (a & sp' & E')]; rewrite E' in He; discriminate He.
    + apply takes_ret in Hgo as (r' & He & _).
      destruct Hadd as [E' | (a & sp & E')]; rewrite E' in He; discriminate He.
    + destruct (takes_ended Hgo).
    + exact Hdone.
  - (* a call of the code is no single event *)
    rewrite Hcall in Hat. discriminate Hat.
  - (* the call returns at w *)
    assert (direct c from (history (w - 1))) as Hdirect by (rewrite Hend; cbn; auto).
    pose proof (Hlater _ Hdirect) as Hw.
    pose proof (Htakes _ Hw (or_introl Hdirect)) as Hgo. rewrite Hend in Hgo.
    destruct (Hwalk _ _ (Hsteps _ Hw)) as [[K E] | [(w1 & ty & K & E & Hw1) | [[e E] | [E | Hdone]]]];
      try (rewrite E in Hgo).
    + exfalso. refine (respond_call _ Hgo). exact I.
    + pose proof (respond_waiting Hgo). lia.
    + destruct (respond_ret Hgo).
    + destruct (takes_ended Hgo).
    + destruct Hdone as (a & b & [Ha Hb] & Hd). exists a, b. split; [lia | exact Hd].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma startThreadReadsTheFlagUnset_Proofs_feasible : startThreadReadsTheFlagUnset_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h code w [[who H] | [who H]]; destruct (nothing_called_at_rest _ _ _ H). }
  intros h. repeat split; intros w by_ inside found H; discriminate H.
Qed.
