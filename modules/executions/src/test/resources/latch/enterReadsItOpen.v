Require Export FrFlowGen.Latch.enterReadsItOpen.Spec.
Require Import FrFlowGen.Latch.Domain.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Of a call of `enter`: a response that is a return comes after a read of the flag that gave false. *)
Lemma enterReadsItOpen_Proofs_complete : enterReadsItOpen_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hflag l from response to [who Hdone] ->.
  assert (exists r, names N l (vref "frflow.executions.latch.Latch" r)) as [r Hl].
  { destruct (Hmade l from) as (m & b & ins & hs & _ & Hmk); [| exact (made_named C Hmk)].
    assert (calledBy history (Invocation_mk L.Latch_enter [l]) who from) as Hc
      by (destruct Hdone as [[Hat _] | [Hcall _]]; [right; eexists; exact Hat | left; exact Hcall]).
    unfold calledOn. eauto 14. }
  destruct Hdone as [[(inside & spawns & Hat) _] | [[inside Hcall] [spawns Hend]]].
  { exfalso. exact (method_not_atomic C (Member "frflow.executions.latch.Latch" "enter" ":scala.Unit") Hat Hl
      eq_refl). }
  replace to with (to - 1 + 1) by lia.
  refine (method_meets (fun w => forall sp, history w = Event_Respond who from (Response_Returned Value_Unit_) sp ->
      exists a b, (from <= a /\ b <= w + 1) /\ exists who', completedBy history
        (Invocation_mk L.AtomicBoolean_get
          [heldIn L.Latch_closed l]) who' a (Response_Returned (Value_Bool_ False)) b)
    C (Member "frflow.executions.latch.Latch" "enter" ":scala.Unit") Hcall Hl eq_refl _ (to - 1) _ spawns Hend);
    [| rewrite Hend; cbn; auto].
  intros args w Hargs _. inversion Hargs; subst.
  (* the flag is read *)
  step. intros w1 v y Hw1 _ Hy Hty Hread. split; [miss |]. apply (Hflag l) in Hread. subst y. typed Hty.
  (* and asked what it holds *)
  step. intros w2 ys Hw2 _ Hys Hmk. split; [miss |]. intros w3 a x Hw3 Hget Hgives Htyped.
  apply args_one in Hys as (y0 & -> & Hy0). rewrite (one_name N _ _ _ Hy0 Hy) in Hget.
  (* it threw, or it is set: `enter` throws; it is unset: `enter` returns, and this read is the one *)
  step; [miss | miss |]. intros r' Hw _ _ _ sp _.
  destruct a as [answer | thrown]; [| contradiction]. apply named_bool in Hgives. subst answer.
  exists w2, w3. split; [lia |]. exists who. unfold completedBy, doneAtOnce, begun.
  destruct Hget as [(sp' & Hat & ->) | (Hinv & _ & sp' & Hresp)]; [left | right]; eauto.
Qed.

(** An execution in which nothing happens meets what the step is from. *)
