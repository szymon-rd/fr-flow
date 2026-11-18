Require Export FrFlowGen.OxThreads.whoAddsIsCallingStartThread.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The add is one a call of startThread itself made; that call is pending when it makes it, and has not
    completed while the add is pending. *)
Lemma whoAddsIsCallingStartThread_Proofs_complete : whoAddsIsCallingStartThread_Obl_complete.
Proof.
  intros heldIn history _ Honly Hruns Hpending h t c w b [Hherd [Hcalled | (a & Ha & Hbegun & Hnotover)]].
  - destruct (Honly h t c w b (conj Hherd Hcalled)) as (code & from & Hc & Hit). exists code.
    exact (Hruns h code c t from w (conj Hc Hit)).
  - destruct (Honly h t c a b (conj Hherd (or_introl Hbegun))) as (code & from & Hc & Hit). exists code, from.
    exact (Hpending h code c t from a w (conj (conj Hc Hit) (conj Ha (conj Hbegun Hnotover)))).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
