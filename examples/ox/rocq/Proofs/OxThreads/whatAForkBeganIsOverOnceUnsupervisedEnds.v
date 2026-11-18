Require Export FrFlowGen.OxThreads.whatAForkBeganIsOverOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so what a fork of it began while running
    its code is over by then. *)
Lemma whatAForkBeganIsOverOnceUnsupervisedEnds_Proofs_complete : whatAForkBeganIsOverOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
