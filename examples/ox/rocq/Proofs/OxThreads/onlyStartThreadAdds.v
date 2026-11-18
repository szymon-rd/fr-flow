Require Export FrFlowGen.OxThreads.onlyStartThreadAdds.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who adds to a herd's set is a call of startThread, which is pending when it does; and the thread added has
    not been started. *)
Lemma onlyStartThreadAdds_Proofs_complete : onlyStartThreadAdds_Obl_complete.
Proof.
  intros heldIn history _ Honly Hruns Hnot h t c w b Hadd.
  split; [| exact (Hnot h t c w b Hadd)].
  destruct (Honly h t c w b Hadd) as (code & from & Hstart & Hitself).
  exists code. exact (Hruns h code c t from w (conj Hstart Hitself)).
Qed.
