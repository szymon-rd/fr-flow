Require Export FrFlowGen.OxThreads.whatAForkBeganIsOverOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment supervised completes: so what a fork of it began while running
    its code is over by then. *)
Lemma whatAForkBeganIsOverOnceSupervisedEnds_Proofs_complete : whatAForkBeganIsOverOnceSupervisedEnds_Obl_complete.
Proof.
  intros heldIn history _ Hcloses Hover c s from to t forked inner m [[[Hmade Hfork] Hrunning] Hinner].
  apply (Hover (heldIn L.OxError_herd s) t forked inner m to).
  split; [split; [split; [exact (Hcloses c s from to Hmade) | exact Hfork] | exact Hrunning] | exact Hinner].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
