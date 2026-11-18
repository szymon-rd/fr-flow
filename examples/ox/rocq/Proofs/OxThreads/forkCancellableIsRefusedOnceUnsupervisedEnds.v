Require Export FrFlowGen.OxThreads.forkCancellableIsRefusedOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so a call of forkCancellable in the scope,
    made from then on, does not return. *)
Lemma forkCancellableIsRefusedOnceUnsupervisedEnds_Proofs_complete :
  forkCancellableIsRefusedOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros history heldIn _ Hcloses Hrefuses c s from to code d m fork w [[Hmade Hle] Hcalled].
  apply (Hrefuses code s d m fork w). split; [| exact Hcalled].
  destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
  exists f0, e0, t0. split; [lia | exact Hclosed].
Qed.
