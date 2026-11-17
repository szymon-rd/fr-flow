Require Export FrFlowGen.OxThreads.noRaceOnAScopesVals.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Code.Conforms FrFlow.Code.Walk.

(** A val of a scope is being written by a thread only if that thread marked it, so made the scope. Another
    thread that marks or writes it made the scope too, and a scope is made once: it is the same thread. Another
    thread that reads it does so once the scope's constructor has returned it, and then no val of it is being
    written. *)
Lemma noRaceOnAScopesVals_Proofs_complete : noRaceOnAScopesVals_Obl_complete.
Proof.
  intros history [N C] Hsettled Hconstructed Hassigned s field Hfield by_ other inside w
    [Hwriting [Hassigns | Hreads]].
  - destruct Hwriting as (m & ins & [Hm Hmark] & _).
    destruct (Hassigned s field by_ ins m (conj Hfield (or_introl Hmark))) as (m1 & cls1 & hs1 & _ & Hmade1).
    destruct (Hassigned s field other inside w (conj Hfield Hassigns)) as (m2 & cls2 & hs2 & _ & Hmade2).
    pose proof (made_at_one C Hmade1 Hmade2) as ->. rewrite Hmade1 in Hmade2.
    injection Hmade2 as -> _ _ _. reflexivity.
  - exfalso. pose proof (Hconstructed s field other inside w (conj Hfield Hreads)) as Hr.
    destruct (Hsettled s w Hr field by_ inside w (conj Hfield (Z.le_refl w))) as [Hnot _]. exact (Hnot Hwriting).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma noRaceOnAScopesVals_Proofs_feasible : noRaceOnAScopesVals_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros s w (x & x1 & x2 & x3 & x4 & x5 & c & from & to & _ & H).
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s field by_ inside w [_ [v H]]. discriminate H. }
  intros s field by_ inside w [_ [H | [v H]]]; discriminate H.
Qed.
