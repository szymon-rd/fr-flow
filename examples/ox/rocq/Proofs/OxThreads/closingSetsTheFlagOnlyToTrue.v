Require Export FrFlowGen.OxThreads.closingSetsTheFlagOnlyToTrue.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree, gone through whole: its one call of `set`
    is of the flag to true. What it does besides is a check, reads, two variables made, its loop (each turn
    asks the set whether it is empty and traverses it twice), and at the end a read of the exception it kept,
    thrown if there is one. *)
Lemma closingSetsTheFlagOnlyToTrue_Proofs_complete : closingSetsTheFlagOnlyToTrue_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h v c from w [Hcalled Hsets].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled)
    as (r & inside & Hh & Hcall).
  refine (method_meets
    (fun k => forall s v, itselfMakes history (Invocation_mk
      L.AtomicBoolean_set [s; Value_Bool_ v]) c from k -> v)
    C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") Hcall Hh eq_refl _ w
    (makes_direct Hsets) _ v Hsets).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* the check; the flag is read *)
  pass_to L.AtomicBoolean_set.
  (* and set: to true *)
  step. intros ws yss _ _ Hyss Hmk. split.
  { intros s v' Hit. pose proof (makes_one Hmk Hit) as E. injection E as ->.
    apply args_two in Hyss as (y1 & y2 & E & _ & Hy2). injection E as <- <-.
    apply bool_named in Hy2. exact (proj2 Hy2 eq_refl). }
  (* its two variables are made; then its loop: a turn reads the set, asks whether it is empty, and on a no
     traverses it twice; past the loop the exception kept is read, and thrown if there is one *)
  intros. repeat pass. apply meets_iter with (J := fun _ _ _ => True); [| exact I]. intros tr1 wt s1 _ IH.
  repeat pass. apply IH; [lia | exact I].
Qed.
