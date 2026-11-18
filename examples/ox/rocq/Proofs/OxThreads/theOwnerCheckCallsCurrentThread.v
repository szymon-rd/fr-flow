Require Export FrFlowGen.OxThreads.theOwnerCheckCallsCurrentThread.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.assertOnOwnerThread`'s tree, gone through whole: it asks for the current thread, reads
    the herd's owner, and returns or throws. *)
Lemma theOwnerCheckCallsCurrentThread_Proofs_complete : theOwnerCheckCallsCurrentThread_Obl_complete.
Proof.
  intros history [N C] Hmade h from inner w (who & Hbegun & Hmakes).
  pose proof (begun_is_called _ _ _ _ Hbegun) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "assertOnOwnerThread" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes) as Hdirect. revert inner Hmakes. revert w Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "assertOnOwnerThread" ":scala.Unit") Hcall Hh
    eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  step. intros wcur ys _ _ Hys Hmk1. apply args_none in Hys as ->.
  split; [intros inner Hmk; rewrite <- (makes_one Hmk1 Hmk); reflexivity |]. intros wgot rcur xcur _ _ _ Hretcur.
  repeat pass.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
