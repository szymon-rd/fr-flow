Require Export FrFlowGen.OxThreads.Whole.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** What the model states at the bottom can hold together: a run in which nothing happens, of sets with nothing
    in them, meets each. It shows the statements do not contradict each other, and no more: that the runs of Ox's
    code meet them is what proving the claims of the code will show. *)
Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  exists (fun _ x => x), (fun _ => Step_Rests), (fun _ _ _ => False).
  split.
  { intros h t code made w H. destruct (none_made_to_run_at_rest _ _ _ _ _ H). }
  split.
  { intros h from answer to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h t c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c w (m & _ & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h t c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros w _. reflexivity. }
  split.
  { intros s x. split; intros w who H; destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s x y from answer to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s x y from answer to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros s a b y [_ H]. destruct H. reflexivity.
Qed.
