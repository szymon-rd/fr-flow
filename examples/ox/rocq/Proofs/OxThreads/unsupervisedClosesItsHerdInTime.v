Require Export FrFlowGen.OxThreads.unsupervisedClosesItsHerdInTime.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The call makes a scope and comes to running a function it writes in it. That function ends once the code
    does. So this is a call running code in a scope by the thread that made the scope, whose code ends: it
    closes the scope's herd in time. *)
Lemma unsupervisedClosesItsHerdInTime_Proofs_complete : unsupervisedClosesItsHerdInTime_Obl_complete.
Proof.
  intros heldIn history _ Hclosed Hcomes Hends locals code c from [Hcalled Hcode].
  destruct (Hcomes locals code c from Hcalled)
    as (supervisor & errorMode & parent & s & g & a & b & k & [Hmade Hk] & Hrun).
  destruct (Hclosed supervisor errorMode parent locals s g c a b k) as (k' & [Hk' Hclosing] & Hresp).
  { split; [split; [exact Hmade |] |].
    - destruct Hrun as [H | (r & sp & H)]; [left; exists (Some from); exact H |].
      right. exists r, (Some from), sp. exact H.
    - unfold codeEndsIn. intros m [Hm Hm']. assert (from < m) as Hfm by lia.
      exact (Hends locals code c from s g k m (conj (conj (conj (conj Hcalled Hrun) (Hcode s)) Hfm) Hm')). }
  exists s, k'. split; [split; [lia | exact Hclosing] | exact Hresp].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma unsupervisedClosesItsHerdInTime_Proofs_feasible : unsupervisedClosesItsHerdInTime_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros supervisor errorMode parent locals s g c a b from [[H _] _].
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros locals code c from H. destruct (nothing_called_at_rest _ _ _ H). }
  intros locals code c from s g k m [[[[H _] _] _] _]. destruct (nothing_called_at_rest _ _ _ H).
Qed.
