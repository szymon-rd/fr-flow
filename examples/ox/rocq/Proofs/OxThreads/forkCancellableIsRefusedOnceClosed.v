Require Export FrFlowGen.OxThreads.forkCancellableIsRefusedOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** Had the call returned, a call of startThread on the herd that it made itself would have returned: made
    after the herd was closed, which does not return. *)
Lemma forkCancellableIsRefusedOnceClosed_Proofs_complete : forkCancellableIsRefusedOnceClosed_Obl_complete.
Proof.
  intros heldIn history _ Hstarts Hrefuses s from Hclosed code c m fork w [Hle Hcalled] Hdone.
  destruct (Hstarts code s c m fork w Hdone) as (run & a & b & [[[Ha Hb] Hmakes] Hreturned]).
  destruct (Hrefuses (heldIn L.OxError_herd s) from Hclosed run c c a b) as [Hnot _]; [| exact (Hnot Hreturned)].
  split; [lia |].
  destruct Hmakes as [H | (r & sp & H)]; [left; exists (Some m); exact H | right; exists r, (Some m), sp; exact H].
Qed.
