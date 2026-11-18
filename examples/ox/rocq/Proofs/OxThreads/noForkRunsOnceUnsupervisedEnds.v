Require Export FrFlowGen.OxThreads.noForkRunsOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so no fork of it runs its code from then on. *)
Lemma noForkRunsOnceUnsupervisedEnds_Proofs_complete : noForkRunsOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
