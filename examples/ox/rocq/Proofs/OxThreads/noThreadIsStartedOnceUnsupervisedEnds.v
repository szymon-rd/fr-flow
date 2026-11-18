Require Export FrFlowGen.OxThreads.noThreadIsStartedOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so a call of its startThread made from then on does not return, and adds nothing. *)
Lemma noThreadIsStartedOnceUnsupervisedEnds_Proofs_complete : noThreadIsStartedOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
