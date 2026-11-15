Require Export FrFlowGen.OxThreads.startThreadStaysOutOfHerds.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** What a thread calls while it is calling startThread is one of the five calls startThread makes itself, or is
    called during one of them: none of the five closes a herd or removes from a set, and during each the thread
    does neither. *)
Lemma startThreadStaysOutOfHerds_Proofs_complete : startThreadStaysOutOfHerds_Obl_complete.
Proof.
  intros heldIn history _ Hfive Hcheck Htree Hfactory Hjdk Hone h code h1 x.
  split; intros who from w Hpending Hcalled.
  all: destruct (called_under history _ who _ from _ w (Hone who)
    (fun made k Hmade => Hfive h code from made k (ex_intro _ who (conj (proj2 (proj1 Hpending)) Hmade)))
    Hpending Hcalled) as [Hin | (between & m & Hin & Hunder)].
  all: destruct Hin as [[[[E | E] | (f & r & E)] | (s & t & E)] | (t & E)]; try discriminate E; subst between.
  all: first
    [ exact (proj1 (Hcheck h h1 x) who m w Hunder Hcalled) | exact (proj2 (Hcheck h h1 x) who m w Hunder Hcalled)
    | exact (proj1 (Htree h h1 x) who m w Hunder Hcalled) | exact (proj2 (Htree h h1 x) who m w Hunder Hcalled)
    | exact (proj1 (Hfactory f r h1 x) who m w Hunder Hcalled)
    | exact (proj2 (Hfactory f r h1 x) who m w Hunder Hcalled)
    | exact (proj1 (proj2 (proj1 (Hjdk s s t)) h1 x) who m w Hunder Hcalled)
    | exact (proj2 (proj2 (proj1 (Hjdk s s t)) h1 x) who m w Hunder Hcalled)
    | exact (proj1 (proj2 (Hjdk t t t) h1 x) who m w Hunder Hcalled)
    | exact (proj2 (proj2 (Hjdk t t t) h1 x) who m w Hunder Hcalled) ].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma startThreadStaysOutOfHerds_Proofs_feasible : startThreadStaysOutOfHerds_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h code from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h h1 x. split; intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h h1 x. split; intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros f r h1 x. split; intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros b s t. repeat (intros; split). all: intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  intros t outer from inner w [[[_ H] _] _]. destruct (nothing_begun_at_rest _ _ _ H).
Qed.
