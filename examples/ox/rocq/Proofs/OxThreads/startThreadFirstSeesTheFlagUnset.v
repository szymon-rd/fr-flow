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
Lemma startThreadFirstSeesTheFlagUnset_Proofs_feasible : startThreadFirstSeesTheFlagUnset_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ _ => False), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros s b from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
