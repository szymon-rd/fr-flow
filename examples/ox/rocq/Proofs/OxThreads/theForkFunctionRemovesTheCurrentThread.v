Require Export FrFlowGen.OxThreads.theForkFunctionRemovesTheCurrentThread.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk.

(** Proven of `ThreadHerd.startThread`'s tree, twice over. The call of `newThread` that hands a function to the
    factory is the one `startThread` makes, and the function is the one written there: `try t finally
    threads.remove(Thread.currentThread()).discard`. Run, that function calls `remove` once, on the herd's set,
    with what `Thread.currentThread()` has just given it. *)
Lemma theForkFunctionRemovesTheCurrentThread_Proofs_complete :
  theForkFunctionRemovesTheCurrentThread_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hfields h r c t i w
    [[(code & c0 & from0 & m & [Hm Hstart] & Hhand) Hrun] Hrem].
  assert (exists r0, names N h (vref "ox.internal.ThreadHerd" r0)) as [r0 Hh].
  { destruct (Hmade h code from0) as (m' & b & ins & hs & _ & Hmk); [| exact (made_named C Hmk)].
    left. exists c0. exact Hstart. }
  destruct Hstart as [[inside0 Hcall0] | (a0 & inside0 & sp0 & Hat0)].
  2: { exfalso. exact (method_not_atomic C
         (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hat0 Hh eq_refl). }
  destruct (method_steps C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall0 Hh
    eq_refl) as (args & at0 & Hargs & Hpassed & Hlater0 & Hsteps0 & Htakes0).
  inversion Hargs as [| ycode vcode ys0 vs0 Hcode Hrest]; subst. inversion Hrest; subst. clear Hargs Hrest.
  (* what startThread is given by name is a function *)
  assert (exists b sc0, vcode = VCode (Thunk b sc0)) as (b & sc0 & ->).
  { inversion Hpassed as [| p v ps vs Hp Hps]; subst. exact Hp. }
  clear Hpassed.
  (* the call of newThread is an event of the call of startThread, at m *)
  assert (invoked (history m) = Some (Invocation_mk
      "java.util.concurrent.ThreadFactory newThread java.lang.Runnable:java.lang.Thread"
      [heldIn "ox.internal.ThreadHerd threadFactory" h; r]) /\ direct c0 from0 (history m)) as [Hinv0 Hdirect0].
  { destruct Hhand as [E | (a & sp & E)]; rewrite E; cbn; auto. }
  pose proof (Hlater0 _ Hdirect0) as Hm0.
  pose proof (Htakes0 _ Hm0 (or_introl Hdirect0)) as Hgo0.
  pose proof (Hsteps0 _ Hm0) as H0. clear Hsteps0 Htakes0 Hlater0.
  revert Hgo0. generalize (at0 (m + 1)). revert H0. generalize (at0 m). intros st0 H0 st0' Hgo0.
  (* assertNotShuttingDown *)
  walk H0.
  apply step_method in H0 as [[-> _] | (w1 & ys1 & _ & _ & _ & _ & [(-> & _) |
    (w2 & r2 & sp2 & x2 & _ & _ & _ & _ & _ & H0)])].
  { exfalso. apply invoked_method in Hgo0 as (ys & _ & E). rewrite Hinv0 in E. cbn in E. discriminate E. }
  { exfalso. apply invoked_waiting in Hgo0. rewrite Hinv0 in Hgo0. discriminate Hgo0. }
  destruct x2 as [e | v2].
  { exfalso. walk H0. pose proof (ends_quietly H0 Hgo0) as E. rewrite Hinv0 in E. discriminate E. }
  (* verifyCurrentThreadInScopeTree *)
  walk H0.
  apply step_method in H0 as [[-> _] | (w3 & ys3 & _ & _ & _ & _ & [(-> & _) |
    (w4 & r4 & sp4 & x4 & _ & _ & _ & _ & _ & H0)])].
  { exfalso. apply invoked_method in Hgo0 as (ys & _ & E). rewrite Hinv0 in E. cbn in E. discriminate E. }
  { exfalso. apply invoked_waiting in Hgo0. rewrite Hinv0 in Hgo0. discriminate Hgo0. }
  destruct x4 as [e | v4].
  { exfalso. walk H0. pose proof (ends_quietly H0 Hgo0) as E. rewrite Hinv0 in E. discriminate E. }
  (* the factory, read *)
  walk H0.
  apply step_read in H0 as [[-> _] | (w5 & vtf & ytf & yo & _ & _ & Hyo & _ & Hty & _ & H0)].
  { exfalso. apply invoked_read in Hgo0. rewrite Hinv0 in Hgo0. discriminate Hgo0. }
  destruct (read_place Hh Hyo) as [_ Hcls]. rewrite Hcls in Hty. change (receiver vtf = [vtf]) in Hty.
  walk H0.
  apply step_called in H0 as [[-> _] | (w6 & ys6 & _ & _ & _ & [(_ & -> & _) |
    (w7 & a7 & x7 & _ & _ & _ & _ & Hty7 & H0)])].
  2: { exfalso. apply invoked_waiting in Hgo0. rewrite Hinv0 in Hgo0. discriminate Hgo0. }
  2: { (* past its call of newThread, the call of startThread makes no other *)
    exfalso. destruct x7 as [e | thread].
    { walk H0. pose proof (ends_quietly H0 Hgo0) as E. rewrite Hinv0 in E. discriminate E. }
    change (identity thread) in Hty7. pose proof (identity_receiver _ Hty7) as Hthread.
    walk H0.
    apply step_read in H0 as [[-> _] | (w8 & vset & yset & yo8 & _ & _ & Hyo8 & _ & Hty8 & _ & H0)].
    { apply invoked_read in Hgo0. rewrite Hinv0 in Hgo0. discriminate Hgo0. }
    destruct (read_place Hh Hyo8) as [_ Hcls8]. rewrite Hcls8 in Hty8. apply identity_receiver in Hty8.
    walk H0.
    apply step_called in H0 as [[-> _] | (w9 & ys9 & _ & _ & _ & [(_ & -> & _) |
      (w10 & a10 & x10 & _ & _ & _ & _ & _ & H0)])].
    { apply invoked_outside in Hgo0 as (ys & _ & E). rewrite Hinv0 in E. discriminate E. }
    { apply invoked_waiting in Hgo0. rewrite Hinv0 in Hgo0. discriminate Hgo0. }
    destruct x10 as [e | v10].
    { walk H0. pose proof (ends_quietly H0 Hgo0) as E. rewrite Hinv0 in E. discriminate E. }
    walk H0.
    apply step_called in H0 as [[-> _] | (w11 & ys11 & _ & _ & _ & [(_ & -> & _) |
      (w12 & a12 & x12 & _ & _ & _ & _ & _ & H0)])].
    { apply invoked_outside in Hgo0 as (ys & _ & E). rewrite Hinv0 in E. discriminate E. }
    { apply invoked_waiting in Hgo0. rewrite Hinv0 in Hgo0. discriminate Hgo0. }
    destruct x12 as [e | v12]; walk H0; pose proof (ends_quietly H0 Hgo0) as E; rewrite Hinv0 in E;
      discriminate E. }
  (* so the function handed over is the one written in startThread *)
  apply invoked_outside in Hgo0 as (ys & Hys & E). rewrite Hinv0 in E. injection E as E. subst ys.
  inversion Hys as [| yf vf ysf vsf _ Hrest1]; subst. inversion Hrest1 as [| yr vr ysr vsr Hr _]; subst.
  clear Hys Hrest1 Hinv0 Hdirect0 Hhand Hcall0 Hcode Hty Hyo Hcls.
  (* a thread runs it *)
  lazymatch type of Hr with names _ _ (VCode ?fn) =>
    assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  destruct Hrun as [[inside Hcall] | (a & inside & sp & Hat)].
  2: { exfalso. exact (function_not_atomic C Hat eq_refl Hr Hwritten). }
  destruct (function_steps C Hcall eq_refl Hr Hwritten) as (args & at_ & Hargs & Hlater & Hsteps & Htakes).
  inversion Hargs; subst. clear Hargs.
  assert (invoked (history w) = Some (Invocation_mk
      "java.util.concurrent.ConcurrentHashMap$.KeySetView remove java.lang.Object:scala.Boolean"
      [heldIn "ox.internal.ThreadHerd threads" h; t]) /\ direct c i (history w)) as [Hinv Hdirect].
  { destruct Hrem as [E | (a & sp & E)]; rewrite E; cbn; auto. }
  pose proof (Hlater _ Hdirect) as Hw.
  pose proof (Htakes _ Hw (or_introl Hdirect)) as Hgo.
  pose proof (Hsteps _ Hw) as H. clear Hsteps Htakes Hlater.
  revert Hgo. generalize (at_ (w + 1)). revert H. generalize (at_ w). intros st H st' Hgo.
  (* it calls the code it was made to run *)
  walk H.
  apply step_function in H; [| exact I].
  destruct H as [[-> _] | (k1 & n1 & z1 & zs1 & Hk1 & _ & _ & _ & _ & _ & [(-> & _) |
    (k2 & p2 & sq2 & q2 & Hk2 & _ & _ & _ & _ & H)])].
  { exfalso. apply invoked_function in Hgo; [| exact I]. destruct Hgo as (m' & y' & ys' & Hm' & E).
    cbn in Hm'. subst m'. rewrite Hinv in E. discriminate E. }
  { exfalso. apply invoked_waiting in Hgo. rewrite Hinv in Hgo. discriminate Hgo. }
  (* and then, whatever the code gave: the herd's set, read *)
  destruct q2 as [f2 | u2]; walk H.
  all: apply step_read in H as [[-> _] | (k3 & uset & zset & yo2 & Hk3 & _ & Hyo2 & Hzset & Hty2 & Hread2 & H)].
  1, 3: (exfalso; apply invoked_read in Hgo; rewrite Hinv in Hgo; discriminate Hgo).
  all: destruct (read_place Hh Hyo2) as [-> Hcls2]; rewrite Hcls2 in Hty2, Hread2;
    apply (proj2 (proj1 (Hfields h))) in Hread2; subst zset; apply identity_receiver in Hty2.
  (* Thread.currentThread() *)
  all: walk H.
  all: apply step_called in H as [[-> _] | (k4 & zs4 & Hk4 & _ & Hzs4 & [(_ & -> & _) |
    (k5 & b5 & q5 & Hk5 & _ & Hcur & Hgc & Htc & H)])].
  1, 4: (exfalso; apply invoked_outside in Hgo as (ys & _ & E); rewrite Hinv in E; discriminate E).
  1, 3: (exfalso; apply invoked_waiting in Hgo; rewrite Hinv in Hgo; discriminate Hgo).
  all: inversion Hzs4; subst.
  all: destruct q5 as [f5 | current].
  1, 3: (exfalso; walk H; pose proof (ends_quietly H Hgo) as E; rewrite Hinv in E; discriminate E).
  all: change (identity current) in Htc; pose proof (identity_receiver _ Htc) as Hcurrent.
  (* the call of remove *)
  all: walk H.
  all: apply step_called in H as [[-> _] | (k6 & zs6 & Hk6 & _ & Hzs6 & [(_ & -> & _) |
    (k7 & b7 & q7 & Hk7 & _ & _ & _ & _ & H)])].
  2, 5: (exfalso; apply invoked_waiting in Hgo; rewrite Hinv in Hgo; discriminate Hgo).
  2: { (* past it: the result discarded, and the function ends *)
    exfalso. destruct q7 as [f7 | u7].
    { walk H. pose proof (ends_quietly H Hgo) as E. rewrite Hinv in E. discriminate E. }
    walk H.
    apply step_called in H as [[-> _] | (k8 & zs8 & _ & _ & _ & [(_ & -> & _) |
      (k9 & b9 & q9 & _ & _ & _ & _ & _ & H)])].
    { apply invoked_outside in Hgo as (ys & _ & E). rewrite Hinv in E. discriminate E. }
    { apply invoked_waiting in Hgo. rewrite Hinv in Hgo. discriminate Hgo. }
    destruct q9 as [f9 | u9]; walk H; pose proof (ends_quietly H Hgo) as E; rewrite Hinv in E; discriminate E. }
  3: { exfalso. destruct q7 as [f7 | u7].
    { walk H. pose proof (ends_quietly H Hgo) as E. rewrite Hinv in E. discriminate E. }
    walk H.
    apply step_called in H as [[-> _] | (k8 & zs8 & _ & _ & _ & [(_ & -> & _) |
      (k9 & b9 & q9 & _ & _ & _ & _ & _ & H)])].
    { apply invoked_outside in Hgo as (ys & _ & E). rewrite Hinv in E. discriminate E. }
    { apply invoked_waiting in Hgo. rewrite Hinv in Hgo. discriminate Hgo. }
    destruct q9 as [f9 | u9]; walk H; pose proof (ends_quietly H Hgo) as E; rewrite Hinv in E; discriminate E. }
  (* this call of remove is the one: what it removes is what currentThread gave *)
  all: apply invoked_outside in Hgo as (ys & Hys & E); rewrite Hinv in E; injection E as E; subst ys.
  all: inversion Hys as [| ys' vs' ysx vsx _ Hrest]; subst; inversion Hrest as [| yt vt ysy vsy Ht _]; subst.
  all: destruct b5 as [ycur | ythrown]; [| contradiction].
  all: pose proof (one_name N _ _ _ Hgc Ht) as ->.
  all: exists k4, k5; split; [lia |]; unfold completedBy, doneAtOnce, begun.
  all: destruct Hcur as [(sp' & Hat' & ->) | (Hinv' & _ & sp' & Hresp')]; [left | right]; eauto.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma theForkFunctionRemovesTheCurrentThread_Proofs_feasible :
  theForkFunctionRemovesTheCurrentThread_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h code w [[who H] | [who H]]; destruct (nothing_called_at_rest _ _ _ H). }
  intros h. repeat split; intros w by_ inside found H; discriminate H.
Qed.
