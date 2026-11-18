Require Export FrFlowGen.Latch.Whole.Spec.
From Stdlib Require Import ZArith Lia.
Require Import FrFlow.Rules.Walk.

(** An execution in which nothing happens is one of the code, and meets every assumption. *)
Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  exists (fun _ _ => False), (fun _ => Event_Stutter), (fun _ x => x).
  split; [apply nothing_runs |]. repeat split.
  - intros s b from response to [who [[(inside & spawns & H) _] | [[inside H] _]]]; discriminate H.
  - intros l w H. repeat (destruct H as [H | H]);
      destruct H as (rest & by_ & [[inside H] | (a & inside & spawns & H)]); discriminate H.
  - intros l w by_ inside found H. discriminate H.
Qed.
