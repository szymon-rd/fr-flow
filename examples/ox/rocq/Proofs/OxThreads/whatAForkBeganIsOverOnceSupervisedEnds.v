Require Export FrFlowGen.OxThreads.whatAForkBeganIsOverOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment supervised completes: so what a fork of it began while running
    its code is over by then. *)
Lemma whatAForkBeganIsOverOnceSupervisedEnds_Proofs_complete : whatAForkBeganIsOverOnceSupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
