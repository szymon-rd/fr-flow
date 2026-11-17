Require Export FrFlowGen.OxThreads.forkCancellableIsRefusedOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment supervised completes: so a call of forkCancellable in the scope,
    made from then on, does not return. *)
Lemma forkCancellableIsRefusedOnceSupervisedEnds_Proofs_complete :
  forkCancellableIsRefusedOnceSupervisedEnds_Obl_complete.
Proof.
  intros history heldIn _ Hcloses Hrefuses c s from to code d m fork w [[Hmade Hle] Hcalled].
  apply (Hrefuses code s d m fork w). split; [| exact Hcalled].
  destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
  exists f0, e0, t0. split; [lia | exact Hclosed].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma forkCancellableIsRefusedOnceSupervisedEnds_Proofs_feasible :
  forkCancellableIsRefusedOnceSupervisedEnds_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter), (fun _ x => x).
  split; [exact rest_runs |].
  split.
  { intros c s from to (supervisor & errorMode & parent & locals & code & ended & a & b & [[H _] _]).
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros code s c m fork w [_ H]. destruct (nothing_called_at_rest _ _ _ H).
Qed.
