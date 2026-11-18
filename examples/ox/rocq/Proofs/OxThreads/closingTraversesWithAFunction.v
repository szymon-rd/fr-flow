Require Export FrFlowGen.OxThreads.closingTraversesWithAFunction.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree: each of the two traversals a turn of its
    loop makes is given a function written there, which is no null. *)
Lemma closingTraversesWithAFunction_Proofs_complete : closingTraversesWithAFunction_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h f w (from & a & [[_ Hcalled] Hmakes]).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes) as Hdirect. revert f Hmakes. revert a Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* the check that the caller is the owner; the flag is read, and set; the two variables are made *)
  repeat pass. meets_head. apply meets_iter with (J := fun _ w _ => from < w); [| lia].
  intros tr1 wt s1 HJ IH.
  (* a turn: the set is read, and asked whether it is empty *)
  pass. pass. meets_head; [pass | repeat pass |].
  (* not empty: the set is read and traversed, twice; each traversal is given a function written here *)
  pass.
  step. intros wt1 yst1 Hwt1 _ Hyst1 Hmk1. apply args_two in Hyst1 as (yseta & yfuna & -> & _ & Hyfuna).
  split; [intros f Hit E; pose proof (makes_one Hmk1 Hit) as E'; injection E' as _ ->; subst f;
    pose proof (names_one N _ _ _ Hyfuna (of_null N)) as E'; discriminate E' |].
  intros wu1 rt1 xt1 Hwu1 _ _ _. meets_head; [pass |].
  pass.
  step. intros wt2 yst2 Hwt2 _ Hyst2 Hmk2. apply args_two in Hyst2 as (ysetb & yfunb & -> & _ & Hyfunb).
  split; [intros f Hit E; pose proof (makes_one Hmk2 Hit) as E'; injection E' as _ ->; subst f;
    pose proof (names_one N _ _ _ Hyfunb (of_null N)) as E'; discriminate E' |].
  intros wu2 rt2 xt2 Hwu2 _ _ _. meets_head; [pass |].
  (* then the next turn *)
  apply IH; lia.
Qed.
