Require Export FrFlowGen.Latch.enterReadsItOpen.Spec.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk.

Lemma enterReadsItOpen_Proofs_complete : enterReadsItOpen_Obl_complete.
Proof.
  intros heldIn history [N C] Hafter Hmade Hflag l from response to [who Hdone] ->.
  assert (exists r, names N l (vref "frflow.executions.latch.Latch" r)) as [r Hl].
  { destruct (Hmade l from) as (m & b & ins & hs & _ & Hmk); [| exact (made_named C _ Hmk)].
    exists who. destruct Hdone as [[Hat _] | [Hcall _]]; [right; eexists; exact Hat | left; exact Hcall]. }
  destruct Hdone as [[(inside & spawns & Hat) _] | [[inside Hcall] [spawns Hend]]].
  { exfalso. exact (@method_not_atomic _ _ _ _ C from who inside
      (Member "frflow.executions.latch.Latch" "enter" ":scala.Unit") _ r _ l [] [] _ _ Hat Hl eq_refl
      (Forall2_nil _) (Forall2_nil _)). }
  pose proof (Hafter _ _ _ _ _ Hend) as Hlate.
  destruct (@method_steps _ _ _ _ C who inside (Member "frflow.executions.latch.Latch" "enter" ":scala.Unit")
    "frflow.executions.latch.Latch" r _ l [] [] from Hcall Hl eq_refl (Forall2_nil _) (Forall2_nil _))
    as (at_ & Hsteps & Htakes).
  pose proof (Hsteps (to - 1) ltac:(lia)) as H.
  assert (takes Code_table N who from (to - 1) (Event_Respond who from (Response_Returned Value_Unit_) spawns)
    (at_ (to - 1)) (at_ (to - 1 + 1))) as Hgo.
  { rewrite <- Hend. apply Htakes; [lia |]. left. rewrite Hend. cbn. auto. }
  clear Hsteps Htakes. revert Hgo. generalize (at_ (to - 1 + 1)). revert H. generalize (at_ (to - 1)).
  intros st H st' Hgo.
  (* the flag is read *)
  walk H. apply step_read in H as [[-> _] | (w1 & v & y & yo & Hw1 & _ & Hyo & Hy & Hty & Hread & H)].
  { exfalso. refine (respond_vis _ Hgo). intros []. }
  destruct (read_place Hl Hyo) as [-> Hcls]. rewrite Hcls in Hty, Hread.
  apply (Hflag l) in Hread. subst y.
  apply identity_receiver in Hty.
  (* and asked what it holds *)
  walk H.
  apply step_called in H as [[-> _] | (w2 & ys & Hw2 & _ & Hys & [(_ & -> & _) |
    (w3 & a & x & Hw3 & _ & Hget & Hgives & Htyped & H)])].
  { exfalso. refine (respond_vis _ Hgo). intros []. }
  { exfalso. pose proof (respond_waiting Hgo). lia. }
  inversion Hys as [| y0 v0 ys0 vs0 Hy0 Hrest]; subst. inversion Hrest; subst.
  rewrite (one_name N _ _ _ Hy0 Hy) in Hget.
  destruct x as [e | answer].
  { (* the read threw: so does `enter` *)
    exfalso. walk H. exact (ends_with H Hgo). }
  cbn in Htyped. destruct Htyped as [flag ->]. destruct flag.
  { (* the flag is set: `enter` throws *)
    exfalso. walk H. exact (ends_with H Hgo). }
  (* the flag is unset: this read is the one *)
  destruct a as [answer | thrown]; [| contradiction]. apply named_bool in Hgives. subst answer.
  exists w2, w3. split; [lia |]. exists who. unfold completedBy, doneAtOnce, begun.
  destruct Hget as [(sp & Hat & ->) | (Hinv & _ & sp & Hresp)]; [left | right]; eauto.
Qed.

(** An execution in which nothing happens meets what the step is from. *)
Lemma enterReadsItOpen_Proofs_feasible : enterReadsItOpen_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter). split; [apply nothing_runs |]. repeat split.
  - intros by_ made a spawns k H. discriminate H.
  - intros l w [who [[inside H] | (a & inside & spawns & H)]]; discriminate H.
  - intros l w by_ inside found H. discriminate H.
Qed.
