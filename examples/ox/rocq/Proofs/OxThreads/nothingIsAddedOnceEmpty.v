Require Export FrFlowGen.OxThreads.nothingIsAddedOnceEmpty.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who adds a thread is calling startThread, so is inside: the owner, who has not called closing; or a fork that
    has not left, which is in the set if it was added before the set was empty, and was not added after. *)
Lemma nothingIsAddedOnceEmpty_Proofs_complete : nothingIsAddedOnceEmpty_Obl_complete.
Proof.
  intros heldIn history elements _ Hlive Hstay Honly h t m w [[Hclosing Hempty] Hmw].
  revert t. pattern w. apply (Zlt_lower_bound_ind _ m); [| exact Hmw].
  intros x IH Hx t (who & Hadd).
  destruct (Honly h t who x Hadd) as [(code & m0 & Hm0 & Hbegun & Hpending) _].
  assert (inside heldIn history who h x) as Hin.
  { apply (Hstay h code who x). right. exists m0. split; [exact Hm0 | split; [exact Hbegun | exact Hpending]]. }
  destruct Hin as [[Hown Hnot] | [(a & Ha & who' & Hadd') Hstays]].
  - apply Hnot. destruct Hclosing as (m1 & Hm1 & Hc1). exists m1. split; [lia | exact Hc1].
  - assert (a < m \/ m <= a) as [Hlt | Hge] by lia.
    + apply (Hempty who). apply (Hlive h who m). split.
      * exists a. split; [exact Hlt | exists who'; exact Hadd'].
      * intros (r & Hr & Hrem). apply Hstays. exists r. split; [lia | exact Hrem].
    + apply (IH a ltac:(lia) who). exists who'. exact Hadd'.
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
Lemma nothingIsAddedOnceEmpty_Proofs_feasible : nothingIsAddedOnceEmpty_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h t w [H _]. destruct (no_fork_at_rest _ _ _ _ H). }
  split.
  { intros h code c w [H | (m & _ & H & _)];
      [destruct (nothing_called_at_rest _ _ _ H) | destruct (nothing_begun_at_rest _ _ _ H)]. }
  intros h t c w H. destruct (nothing_called_at_rest _ _ _ H).
Qed.
