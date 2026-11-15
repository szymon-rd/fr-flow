Require Export FrFlowGen.Latch.enterFindsItOpen.Spec.
From Stdlib Require Import ZArith Lia.
Require Import FrFlow.Code.Walk.

Lemma enterFindsItOpen_Proofs_complete : enterFindsItOpen_Obl_complete.
Proof.
  intros flag heldIn history _ Hreads Hget l from response to Hdone ->.
  destruct (Hreads l from _ to Hdone eq_refl) as (a & b & [Ha Hb] & Hcall).
  destruct (Hget _ False a _ b Hcall eq_refl) as (m & [Hm1 Hm2] & Hflag).
  exists m. split; [lia |]. rewrite Hflag. intros [].
Qed.

(** An execution in which nothing happens meets what the step is from. *)
Lemma enterFindsItOpen_Proofs_feasible : enterFindsItOpen_Obl_feasible.
Proof.
  exists (fun _ _ => False), (fun _ x => x), (fun _ => Event_Stutter). split; [apply nothing_runs |]. split.
  - intros l from response to [who [[(inside & spawns & H) _] | [[inside H] _]]]; discriminate H.
  - intros s b from response to [who [[(inside & spawns & H) _] | [[inside H] _]]]; discriminate H.
Qed.
