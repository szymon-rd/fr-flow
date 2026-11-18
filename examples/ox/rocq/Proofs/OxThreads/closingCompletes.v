Require Export FrFlowGen.OxThreads.closingCompletes.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The call is on a herd that has been made, whose set comes to rest empty once closing has traversed it with no
    call adding to it in progress: so the call is responded to. *)
Lemma closingCompletes_Proofs_complete : closingCompletes_Obl_complete.
Proof.
  intros heldIn history elements _ Hcompletes Hempties Hcons h from Hcalled.
  apply (Hcompletes h from). split; [exact Hcalled |].
  apply (Hempties h from). apply (Hcons h from). left. left. left. left. right. unfold calledOn. eauto 14.
Qed.

(** What it is from can hold: an execution in which nothing happens meets each. *)
