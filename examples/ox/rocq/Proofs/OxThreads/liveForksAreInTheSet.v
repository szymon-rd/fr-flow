Require Export FrFlowGen.OxThreads.liveForksAreInTheSet.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The set of a herd is a set: what was added to it and not removed from it is in it. *)
Lemma liveForksAreInTheSet_Proofs_complete : liveForksAreInTheSet_Obl_complete.
Proof.
  intros elements heldIn history Hstart Hatomic Hadd Hrem Honly h t w [Hfork Hleft].
  set (s := heldIn "ox.internal.ThreadHerd threads"%string h) in *.
  eapply (added_and_not_removed_is_in history (elements s)).
  - exact Hstart.
  - intros x. exact (Hatomic s x).
  - intros x y. exact (Hadd s x y).
  - intros x y. exact (Hrem s x y).
  - intros a b y. exact (Honly s a b y).
  - exact Hfork.
  - exact Hleft.
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
Lemma liveForksAreInTheSet_Proofs_feasible : liveForksAreInTheSet_Obl_feasible.
Proof.
  exists (fun _ _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
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
