Require Export FrFlowGen.OxThreads.forkUnsupervisedIsRefusedOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so a call of forkUnsupervised in the scope,
    made from then on, does not return. *)
Lemma forkUnsupervisedIsRefusedOnceUnsupervisedEnds_Proofs_complete :
  forkUnsupervisedIsRefusedOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros history heldIn _ Hcloses Hrefuses c s from to code d m fork w [[Hmade Hle] Hcalled].
  apply (Hrefuses code s d m fork w). split; [| exact Hcalled].
  destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
  exists f0, e0, t0. split; [lia | exact Hclosed].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
