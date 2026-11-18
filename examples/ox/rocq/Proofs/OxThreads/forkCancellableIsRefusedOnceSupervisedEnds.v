Require Export FrFlowGen.OxThreads.forkCancellableIsRefusedOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment supervised completes: so a call of forkCancellable in the scope,
    made from then on, does not return. *)
Lemma forkCancellableIsRefusedOnceSupervisedEnds_Proofs_complete :
  forkCancellableIsRefusedOnceSupervisedEnds_Obl_complete.
Proof.
  intros ? ? _ Hcloses Hlaw c s from to Hmade.
  exact (Hlaw _ to (Hcloses c s from to Hmade)).
Qed.
