Require Export FrFlowGen.Sets.Whole.Spec.
Require Export Proofs.Sets.Lemmas.

(** A run in which nothing happens, of sets with nothing in them, meets every assumption. *)
Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  exists (fun _ => Step_Rests), (fun _ _ _ => False). repeat split.
  - intros w who H. destruct (nothing_called_at_rest _ _ _ H).
  - intros w who H. destruct (nothing_called_at_rest _ _ _ H).
  - intros s x y from answer to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H).
  - intros s x y from answer to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H).
  - intros s a b y [_ H]. destruct H. reflexivity.
Qed.

(** A run whose first step adds to a set has something added and not removed. *)
Lemma Whole_Proofs_satisfiable_1_whoIsAddedStays : Whole_Obl_satisfiable_1_whoIsAddedStays.
Proof.
  exists (fun m => ite (m = 0)
    (Step_Does Thing_NoValue None (Invocation_mk "KeySet.add"%string [Thing_NoValue; Thing_NoValue])
      (Answer_Returned Thing_NoValue) [])
    Step_Rests).
  exists Thing_NoValue, Thing_NoValue, 1. repeat split.
  - exists 0. split; [lia |]. exists Thing_NoValue. right. exists (Answer_Returned Thing_NoValue), None, [].
    rewrite ite_true; reflexivity.
  - intros (m & _ & who & [(inside & H) | (a & inside & hands & H)]).
    + destruct (classic (m = 0)) as [E | E]; [rewrite ite_true in H by exact E | rewrite ite_false in H by exact E];
        discriminate.
    + destruct (classic (m = 0)) as [E | E]; [rewrite ite_true in H by exact E | rewrite ite_false in H by exact E];
        discriminate.
Qed.
