Require Export FrFlowGen.OxThreads.aClosedHerdRefusesToStart.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing set the flag, and it stays set. A call of startThread made after that never sees it unset, so it
    neither adds a thread nor returns. *)
Lemma aClosedHerdRefusesToStart_Proofs_complete : aClosedHerdRefusesToStart_Obl_complete.
Proof.
  intros heldIn history flag Hsets Hstays Hsees Hafter h code c t from response to Hdone [Hcalled Hnotpending].
  destruct (called_and_over_completed history _ _ from Hcalled Hnotpending)
    as (from' & response' & to' & Hclosed & _ & Hle).
  assert (forall m, from <= m -> flag (heldIn "ox.internal.ThreadHerd shutdownInProgress"%string h) m) as Hset.
  { intros m Hm. pose proof (Hsets h from' response' to' Hclosed) as Hat.
    assert (to' = m \/ to' < m) as [<- | Hlt] by lia; [exact Hat | apply (Hstays h to' m); split; assumption]. }
  pose proof (completed_was_called _ _ _ _ _ _ Hdone) as Hstart.
  split.
  - intros ->.
    assert (from < to) as Hft.
    { destruct Hdone as [[_ ->] | [_ (spawns & Hs)]]; [lia |]. pose proof (Hafter _ _ _ _ _ Hs). lia. }
    destruct (Hsees h code c t from to) as (m & [Hm _] & Hunset).
    { split; [split; [exact Hstart | exact Hft] | right; exact Hdone]. }
    apply Hunset. apply Hset. exact Hm.
  - intros (m1 & [Hm1 _] & Hadd).
    assert (from < m1) as Hlt.
    { assert (from = m1 \/ from < m1) as [<- | H] by lia; [| exact H].
      destruct (one_call_at_a_moment history _ _ _ _ from Hadd Hstart) as [E _]. discriminate E. }
    destruct (Hsees h code c t from m1) as (m & [Hm _] & Hunset).
    { split; [split; [exact Hstart | exact Hlt] | left; exact Hadd]. }
    apply Hunset. apply Hset. exact Hm.
Qed.

(** Its parts can hold together: a run in which nothing happens, of flags never set, meets each. *)
Lemma aClosedHerdRefusesToStart_Proofs_feasible : aClosedHerdRefusesToStart_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ => False).
  split.
  { intros h from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h a b [_ H]. exact H. }
  split.
  { intros h code c t from w [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros by_ made a spawns k H. discriminate H.
Qed.
