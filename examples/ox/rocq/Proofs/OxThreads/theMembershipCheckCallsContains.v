Require Export FrFlowGen.OxThreads.theMembershipCheckCallsContains.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.isOwnerOrHerdThread`'s tree, gone through whole: it reads the herd's owner and
    compares it with the thread; if they differ it reads the herd's set and asks whether it contains the thread. *)
Lemma theMembershipCheckCallsContains_Proofs_complete : theMembershipCheckCallsContains_Obl_complete.
Proof.
  intros history [N C] Hmade h t from inner w (who & Hbegun & Hmakes).
  pose proof (begun_is_called _ _ _ _ Hbegun) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "isOwnerOrHerdThread" "java.lang.Thread:scala.Boolean") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes) as Hdirect. revert inner Hmakes. revert w Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "isOwnerOrHerdThread" "java.lang.Thread:scala.Boolean")
    Hcall Hh eq_refl _).
  intros args k Hargs Hpassed. apply vals_one in Hargs as (vt & -> & _).
  inversion Hpassed as [| pt vt' pst vst Hthread _]; subst. typed Hthread.
  (* the owner is read: it is the thread, or the set is read and asked *)
  pass. meets_head; [pass |].
  pass.
  step. intros wask ys _ _ Hys Hmk1. apply args_two in Hys as (yset & ythread & -> & _ & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmk1 Hmk); eauto |]. intros wasked rask xask _ _ _ Hretask.
  repeat pass.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
