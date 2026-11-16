Require Export FrFlowGen.OxThreads.nothingIsAddedOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so nothing is added to its set from then on. *)
Lemma nothingIsAddedOnceUnsupervisedEnds_Proofs_complete : nothingIsAddedOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros heldIn history _ Hcloses Honce c s from to t w [Hmade Hle].
  apply (Honce (heldIn "ox.OxError herd"%string s) t w).
  destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
  exists f0, e0, t0. split; [lia | exact Hclosed].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma nothingIsAddedOnceUnsupervisedEnds_Proofs_feasible : nothingIsAddedOnceUnsupervisedEnds_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros c s from to (supervisor & errorMode & parent & locals & code & ended & a & b & [[H _] _]).
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h t w (from & ended & to & _ & H). destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
