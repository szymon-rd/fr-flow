Require Export FrFlowGen.OxThreads.Whole.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** What the model states at the bottom can hold together: an execution in which nothing happens (which is one of
    the code), of sets with nothing in them and flags never set, meets each. It shows the statements do not
    contradict each other, and no more. *)
Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  exists (fun _ => Event_Stutter), (fun _ x => x), (fun _ _ _ => False), (fun _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros supervisor errorMode parent locals code c s from ended to a b [[H _] _].
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s. split; intros from response to [who H]; destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h finalizers supervisor errorMode parent locals s from response to [who H].
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h code t m w [[who H] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h g r q t i j [[[_ H] _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h a b H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s f c _ from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h who from made by_ w [[[H _] _] _]. destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros t from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros x _ from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros t from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h code c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s v w [[_ H1] H2]. destruct (H1 H2). }
  split.
  { intros h w (x & who & from & to & _ & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros b x from to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h w (x & who & from & to & _ & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s from to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s b from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s b from value to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s b from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h code c t from b m other [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros f r h1 x. split; intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros b s t. repeat (intros; split). all: intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros t s x. repeat (intros; split). all: intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros s. repeat (intros; split). all: intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros t outer from inner w [[[_ H] _] _]. destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H). }
  split.
  { intros h. repeat split; intros w by_ inside written H; discriminate H. }
  split.
  { intros h. repeat split; intros w by_ inside found H; discriminate H. }
  split.
  { intros c from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s x from value to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros s x w [[_ H] _]. destruct H.
Qed.
