Require Export FrFlowGen.OxThreads.aForkRemovesOnlyItself.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who removes a thread from a herd's set is a function startThread made, which removes what
    `Thread.currentThread()` gave it: the thread that runs it. *)
Lemma aForkRemovesOnlyItself_Proofs_complete : aForkRemovesOnlyItself_Obl_complete.
Proof.
  intros heldIn history _ Honly Hfunction Hcurrent h t c w since Hremoves.
  destruct (Honly h t c w since Hremoves) as (r & i & Hrun & Hitself).
  destruct (Hfunction h r c t i w (conj Hrun Hitself)) as (a & b & _ & Hgave).
  pose proof (Hcurrent c a _ b Hgave) as E. injection E. auto.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma aForkRemovesOnlyItself_Proofs_feasible : aForkRemovesOnlyItself_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h t c w b [_ H]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h r c t i w [[_ H] _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros c from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
