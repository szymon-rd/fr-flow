Require Export FrFlowGen.OxThreads.noForkRunsOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so no fork of it runs its code from then on. *)
Lemma noForkRunsOnceUnsupervisedEnds_Proofs_complete : noForkRunsOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros heldIn history _ Hcloses Honce c s from to t forked w [[Hmade Hle] Hfork].
  apply (Honce (heldIn L.OxError_herd s) t forked w). split; [| exact Hfork].
  destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
  exists f0, e0, t0. split; [lia | exact Hclosed].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
