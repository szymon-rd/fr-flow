Require Export FrFlowGen.OxThreads.noForkRunsOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment supervised completes: so no fork of it runs its code from then on. *)
Lemma noForkRunsOnceSupervisedEnds_Proofs_complete : noForkRunsOnceSupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
