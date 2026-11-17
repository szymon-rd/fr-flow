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
Lemma closingCompletes_Proofs_feasible : closingCompletes_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h from [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h made Hready. destruct (nothing_ready_at_rest _ _ _ Hready). }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
