Require Export FrFlowGen.OxThreads.aScopesHerdIsClosedInTime.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The call comes to closing the scope's herd. The herd's owner is the thread that made the scope, which is
    the thread that calls: so that closing is responded to. *)
Lemma aScopesHerdIsClosedInTime_Proofs_complete : aScopesHerdIsClosedInTime_Obl_complete.
Proof.
  intros heldIn history _ Hcompletes Hreached Howner supervisor errorMode parent locals s g c a b from
    [[Hmade Hcalled] Hcode].
  destruct (Hreached s g c from (conj Hcalled Hcode)) as (k & Hk & Hclosing).
  pose proof (Howner supervisor errorMode parent locals c s a b Hmade) as Eowner.
  exists k. split; [split; [exact Hk | exact Hclosing] |].
  rewrite <- Eowner in Hclosing |- *. exact (Hcompletes (heldIn "ox.OxError herd"%string s) k Hclosing).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma aScopesHerdIsClosedInTime_Proofs_feasible : aScopesHerdIsClosedInTime_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h from H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s g c from [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros supervisor errorMode parent locals c s from to H. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
