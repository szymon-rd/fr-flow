Require Export FrFlowGen.OxThreads.noRaceOnClosingsVariables.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Scala.Tree FrFlow.Code.Conforms FrFlow.Rules.Walk.

(** What a call of closing itself makes, only the thread that called closing reads, marks and writes. So the
    thread that is writing such a variable, having marked it, is closing's caller, and so is a thread that reads,
    marks or writes it meanwhile: they are one thread. *)
Lemma noRaceOnClosingsVariables_Proofs_complete : noRaceOnClosingsVariables_Obl_complete.
Proof.
  intros history [N C] Hkeeps Hmade h c from made field [Hcalled Hcreates] by_ other inside w [Hwriting Haccess].
  assert (calledOn history h L.ThreadHerd_interruptAllAndJoinUntilCompleted from) as Hon
    by (unfold calledOn; eauto).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(do 4 left; right; exact Hon)) eq_refl Hcalled) as (r0 & inside0 & _ & Hcall0).
  assert (forall b m, touches history made b m -> b = c) as Honly.
  { intros b m Ht. apply (Hkeeps h c from made b m).
    split; [split; [split; [exists inside0; exact Hcall0 | exact I] | exact Hcreates] | exact Ht]. }
  destruct Hwriting as (m & ins & [_ Hmark] & _).
  assert (by_ = c) as -> by (apply (Honly by_ m); exists ins, field, Value_Null; right; exact Hmark).
  apply (Honly other w).
  destruct Haccess as [[Ha | [v Ha]] | [v Ha]].
  - exists inside, field, Value_Null. right. exact Ha.
  - exists inside, field, v. left. right. exact Ha.
  - exists inside, field, v. left. left. exact Ha.
Qed.
