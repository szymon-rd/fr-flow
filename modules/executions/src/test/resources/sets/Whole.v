Require Export FrFlowGen.Sets.Whole.Spec.
Require Export Proofs.Sets.Lemmas.

(** A run in which nothing happens, of sets with nothing in them, meets every assumption. *)
Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  exists (fun _ _ _ => False), (fun _ => Event_Stutter).
  split.
  { intros s x from value to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros s w y. split; [intros [_ H]; destruct H | intros [H _]; destruct H].
Qed.

(** A run whose first two steps are a call that adds to a set and its return has something added and not
    removed. *)
Lemma Whole_Proofs_satisfiable_1_whoIsAddedStays : Whole_Obl_satisfiable_1_whoIsAddedStays.
Proof.
  exists (fun m => ite (m = 0)
    (Event_Invoke Value_Unit_ None (Invocation_mk "KeySet.add"%string [Value_Unit_; Value_Unit_]))
    (ite (m = 1) (Event_Respond Value_Unit_ 0 (Response_Returned Value_Unit_) []) Event_Stutter)).
  exists Value_Unit_, Value_Unit_, 2. repeat split.
  - exists 0, Value_Unit_, 2. split; [lia |]. exists Value_Unit_. right. split.
    + exists None. rewrite ite_true; reflexivity.
    + exists []. replace (2 - 1) with 1 by lia. rewrite ite_false by lia. rewrite ite_true; reflexivity.
  - intros (m & _ & who & [(inside & H) | (a & inside & spawns & H)]).
    all: destruct (classic (m = 0)) as [E | E]; [rewrite ite_true in H by exact E; discriminate |];
      rewrite ite_false in H by exact E;
      destruct (classic (m = 1)) as [E1 | E1]; [rewrite ite_true in H by exact E1 | rewrite ite_false in H by exact E1];
      discriminate.
Qed.
