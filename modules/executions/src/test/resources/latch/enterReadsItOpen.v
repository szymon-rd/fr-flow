Require Export FrFlowGen.Latch.enterReadsItOpen.Spec.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk.

Lemma enterReadsItOpen_Proofs_complete : enterReadsItOpen_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hflag l from response to [who Hdone] ->.
  assert (exists r, names N l (vref "frflow.executions.latch.Latch" r)) as [r Hl].
  { destruct (Hmade l from) as (m & b & ins & hs & _ & Hmk); [| exact (made_named C Hmk)].
    exists who. destruct Hdone as [[Hat _] | [Hcall _]]; [right; eexists; exact Hat | left; exact Hcall]. }
  destruct Hdone as [[(inside & spawns & Hat) _] | [[inside Hcall] [spawns Hend]]].
  { exfalso. exact (method_not_atomic C (Member "frflow.executions.latch.Latch" "enter" ":scala.Unit") Hat Hl
      eq_refl). }
  destruct (method_steps C (Member "frflow.executions.latch.Latch" "enter" ":scala.Unit") Hcall Hl eq_refl)
    as (args & at_ & Hargs & _ & Hlater & Hsteps & Htakes).
  inversion Hargs; subst.
  assert (direct who from (history (to - 1))) as Hdirect by (rewrite Hend; cbn; auto).
  pose proof (Hlater _ Hdirect) as Hlate.
  pose proof (Hsteps (to - 1) Hlate) as H.
  pose proof (Htakes _ Hlate (or_introl Hdirect)) as Hgo. rewrite Hend in Hgo.
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
  - intros l w [who [[inside H] | (a & inside & spawns & H)]]; discriminate H.
  - intros l w by_ inside found H. discriminate H.
Qed.
