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
  rewrite <- Eowner in Hclosing |- *. exact (Hcompletes (heldIn L.OxError_herd s) k Hclosing).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
