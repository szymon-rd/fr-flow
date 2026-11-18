Require Export FrFlowGen.OxThreads.startThreadFirstSeesTheFlagUnset.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The read that found the flag unset is a call of `get`: the flag was unset at a moment during it. *)
Lemma startThreadFirstSeesTheFlagUnset_Proofs_complete : startThreadFirstSeesTheFlagUnset_Obl_complete.
Proof.
  intros heldIn flag history _ Hreads Hget h code c t from w Hthen.
  destruct (Hreads h code c t from w Hthen) as (a & b & [Ha Hb] & Hcall).
  destruct (Hget _ False a _ b Hcall eq_refl) as (m & [Hm1 Hm2] & Hflag).
  exists m. split; [lia |]. rewrite Hflag. intros [].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
