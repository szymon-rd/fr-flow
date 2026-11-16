Require Export FrFlowGen.OxThreads.closingCallsFour.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree, gone through whole: the check of the owner,
    the flag set to true, and in each turn of the loop the set asked whether it is empty and traversed twice. *)
Lemma closingCallsFour_Proofs_complete : closingCallsFour_Obl_complete.
Proof.
  intros history [N C] Hmade h from inner w (who & Hbegun & Hmakes).
  pose proof (begun_is_called _ _ _ _ Hbegun) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes) as Hdirect. revert inner Hmakes. revert w Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* the check that the caller is the owner, on the herd *)
  step. intros wown ysown Hwown _ Hysown Hinvown. apply args_one in Hysown as (yown & -> & Hyown).
  pose proof (one_name N _ _ _ Hyown Hh) as ->.
  split; [intros inner Hmk; rewrite <- (makes_one (or_introl Hinvown) Hmk); auto 6 |].
  intros wowned rown spown xown Hwowned _ _.
  meets_head; [pass |].
  (* the flag is read, and set to true *)
  pass.
  step. intros wset ysset Hwset _ Hysset Hmkset. apply args_two in Hysset as (yflag & ytrue & -> & _ & Hytrue).
  apply named_bool in Hytrue. cbn in Hytrue. subst ytrue.
  split; [intros inner Hmk; rewrite <- (makes_one Hmkset Hmk); eauto 8 |].
  intros wsetd rset xset Hwsetd _ _ _.
  (* its two variables are made; then it loops *)
  repeat pass. meets_head. apply meets_iter with (J := fun _ w _ => from < w); [| lia].
  intros tr1 wt s1 HJ IH.
  (* a turn: the set is read, and asked whether it is empty *)
  pass.
  step. intros wask ysask Hwask _ Hysask Hmkask. apply args_one in Hysask as (yseta & -> & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmkask Hmk); eauto 8 |].
  intros wasked rask xask Hwasked _ _ Hretask.
  meets_head; [pass | repeat pass |].
  (* not empty: it is read and traversed, twice; then the next turn *)
  pass.
  step. intros wt1 yst1 Hwt1 _ Hyst1 Hmk1. apply args_two in Hyst1 as (ysetb & yfunb & -> & _ & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmk1 Hmk); eauto 8 |].
  intros wu1 rt1 xt1 Hwu1 _ _ _. meets_head; [pass |].
  pass.
  step. intros wt2 yst2 Hwt2 _ Hyst2 Hmk2. apply args_two in Hyst2 as (ysetc & yfunc & -> & _ & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmk2 Hmk); eauto 8 |].
  intros wu2 rt2 xt2 Hwu2 _ _ _. meets_head; [pass |].
  apply IH; lia.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma closingCallsFour_Proofs_feasible : closingCallsFour_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
