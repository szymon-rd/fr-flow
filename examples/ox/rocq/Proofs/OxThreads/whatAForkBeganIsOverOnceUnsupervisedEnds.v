Require Export FrFlowGen.OxThreads.whatAForkBeganIsOverOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The herd of the scope is closed by the moment unsupervised completes: so what a fork of it began while running
    its code is over by then. *)
Lemma whatAForkBeganIsOverOnceUnsupervisedEnds_Proofs_complete : whatAForkBeganIsOverOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros heldIn history _ Hcloses Hover c s from to t forked inner m [[[Hmade Hfork] Hrunning] Hinner].
  apply (Hover (heldIn "ox.OxError herd"%string s) t forked inner m to).
  split; [split; [split; [exact (Hcloses c s from to Hmade) | exact Hfork] | exact Hrunning] | exact Hinner].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma whatAForkBeganIsOverOnceUnsupervisedEnds_Proofs_feasible : whatAForkBeganIsOverOnceUnsupervisedEnds_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros c s from to (supervisor & errorMode & parent & locals & code & ended & a & b & [[H _] _]).
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h t forked inner m w [_ H]. destruct (nothing_begun_at_rest _ _ _ H).
Qed.
