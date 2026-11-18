Require Export FrFlowGen.OxThreads.nothingIsAddedOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment supervised completes: so nothing is added to its set from then on. *)
Lemma nothingIsAddedOnceSupervisedEnds_Proofs_complete : nothingIsAddedOnceSupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
