Require Export FrFlowGen.OxThreads.theClosingCheckCallsGet.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.assertNotShuttingDown`'s tree, gone through whole: it reads the herd's flag, asks it
    with `get`, and returns or throws. *)
Lemma theClosingCheckCallsGet_Proofs_complete : theClosingCheckCallsGet_Obl_complete.
Proof.
  intros history [N C] Hmade h from inner w (who & Hbegun & Hmakes).
  pose proof (begun_is_called _ _ _ _ Hbegun) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "assertNotShuttingDown" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes) as Hdirect. revert inner Hmakes. revert w Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "assertNotShuttingDown" ":scala.Unit") Hcall Hh
    eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* the flag is read, and asked *)
  pass.
  step. intros wget ys _ _ Hys Hmk1. apply args_one in Hys as (yb & -> & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmk1 Hmk); eauto |]. intros wgot rget xget _ _ _ Hretget.
  pass.
Qed.
