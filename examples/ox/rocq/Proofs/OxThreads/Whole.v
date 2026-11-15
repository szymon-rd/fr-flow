Require Export FrFlowGen.OxThreads.Whole.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** What the model states at the bottom can hold together: an execution in which nothing happens (which is one of
    the code), of sets with nothing in them and flags never set, meets each. It shows the statements do not
    contradict each other, and no more. *)
Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False), (fun _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h t code made w H. destruct (none_made_to_run_at_rest _ _ _ _ _ H). }
  split.
  { intros s from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s b from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h f from a b r [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c w (m & _ & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros s v a b [[_ H1] H2]. destruct (H1 H2). }
  split.
  { intros h v c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s b from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s b from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h t c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from b m other [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h t c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code w [[who H] | [who H]]; destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h. repeat split; intros w by_ inside found H; discriminate H. }
  split.
  { intros c from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros w _. reflexivity. }
  split.
  { intros s x. split; intros w who H; destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s x y from response to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s x y from response to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros s a b y [_ H]. destruct H. reflexivity.
Qed.
