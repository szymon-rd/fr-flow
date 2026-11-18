Require Export FrFlowGen.OxThreads.noThreadIsStartedOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so a call of its startThread made from then on does not return, and adds nothing. *)
Lemma noThreadIsStartedOnceUnsupervisedEnds_Proofs_complete : noThreadIsStartedOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros heldIn history _ Hcloses Hrefuses c s from to code d t m w [[Hmade Hle] Hcalled].
  apply (Hrefuses (heldIn L.OxError_herd s) code d t m w). split; [| exact Hcalled].
  destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
  exists f0, e0, t0. split; [lia | exact Hclosed].
Qed.
