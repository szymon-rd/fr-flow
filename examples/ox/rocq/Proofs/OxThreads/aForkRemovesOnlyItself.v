Require Export FrFlowGen.OxThreads.aForkRemovesOnlyItself.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who removes a thread from a herd's set is a function startThread made, which removes what
    `Thread.currentThread()` gave it: the thread that runs it. *)
Lemma aForkRemovesOnlyItself_Proofs_complete : aForkRemovesOnlyItself_Obl_complete.
Proof.
  intros heldIn history _ Honly Hfunction Hcurrent h t c w since Hremoves.
  destruct (Honly h t c w since Hremoves) as (r & i & Hrun & Hitself).
  destruct (Hfunction h r c t i w (conj Hrun Hitself)) as (a & b & _ & Hgave).
  pose proof (Hcurrent c a _ b Hgave) as E. injection E. auto.
Qed.
