Require Export FrFlowGen.OxThreads.onlyStartThreadAdds.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who adds to a herd's set is a call of startThread, which is pending when it does; and the thread added has
    not been started. *)
Lemma onlyStartThreadAdds_Proofs_complete : onlyStartThreadAdds_Obl_complete.
Proof.
  intros heldIn history _ Honly Hruns Hnot h t c w Hadd.
  split; [| exact (Hnot h t c w Hadd)].
  destruct (Honly h t c w Hadd) as (code & from & Hstart & Hitself).
  exists code. exact (Hruns h code c t from w (conj Hstart Hitself)).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma onlyStartThreadAdds_Proofs_feasible : onlyStartThreadAdds_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h t c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h t c w H. destruct (nothing_called_at_rest _ _ _ H).
Qed.
