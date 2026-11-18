Require Export FrFlowGen.OxThreads.forkUnsupervisedIsRefusedOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so a call of forkUnsupervised in the scope,
    made from then on, does not return. *)
Lemma forkUnsupervisedIsRefusedOnceUnsupervisedEnds_Proofs_complete :
  forkUnsupervisedIsRefusedOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
