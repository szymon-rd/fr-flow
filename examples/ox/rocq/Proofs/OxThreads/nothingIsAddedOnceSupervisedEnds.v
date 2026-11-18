Require Export FrFlowGen.OxThreads.nothingIsAddedOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment supervised completes: so nothing is added to its set from then on. *)
Lemma nothingIsAddedOnceSupervisedEnds_Proofs_complete : nothingIsAddedOnceSupervisedEnds_Obl_complete.
Proof.
  intros heldIn history _ Hcloses Honce c s from to t w [Hmade Hle].
  apply (Honce (heldIn L.OxError_herd s) t w).
  destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
  exists f0, e0, t0. split; [lia | exact Hclosed].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
