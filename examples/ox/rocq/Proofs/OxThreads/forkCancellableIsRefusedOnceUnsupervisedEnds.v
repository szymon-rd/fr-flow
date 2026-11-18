Require Export FrFlowGen.OxThreads.forkCancellableIsRefusedOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so a call of forkCancellable in the scope,
    made from then on, does not return. *)
Lemma forkCancellableIsRefusedOnceUnsupervisedEnds_Proofs_complete :
  forkCancellableIsRefusedOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
