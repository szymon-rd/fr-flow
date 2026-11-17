Require Export FrFlowGen.OxThreads.forkCancellableIsRefusedOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** Had the call returned, a call of startThread on the herd that it made itself would have returned: made
    after the herd was closed, which does not return. *)
Lemma forkCancellableIsRefusedOnceClosed_Proofs_complete : forkCancellableIsRefusedOnceClosed_Obl_complete.
Proof.
  intros heldIn history _ Hstarts Hrefuses code s c m fork w [Hclosed Hcalled] Hdone.
  destruct (Hstarts code s c m fork w Hdone) as (run & a & b & [[[Ha Hb] Hmakes] Hreturned]).
  destruct (Hrefuses (heldIn "ox.OxError herd"%string s) run c c a b) as [Hnot _]; [| exact (Hnot Hreturned)].
  split.
  - destruct Hclosed as (f0 & e0 & t0 & Ht0 & H). exists f0, e0, t0. split; [lia | exact H].
  - destruct Hmakes as [H | (r & sp & H)]; [left; exists (Some m); exact H | right; exists r, (Some m), sp; exact H].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma forkCancellableIsRefusedOnceClosed_Proofs_feasible : forkCancellableIsRefusedOnceClosed_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros code s c from fork to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h code c t from w [(f0 & e0 & t0 & _ & H) _]. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
