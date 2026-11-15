Require Export FrFlowGen.Sets.whoIsAddedStays.Spec.
Require Export Proofs.Sets.Lemmas.

(** The call that added it put it in the set at a moment during the call, so before `w`. From there to `w` it
    leaves at no moment: it would leave only during a call that removes it, and none was made before `w`. *)
Lemma whoIsAddedStays_Proofs_complete : whoIsAddedStays_Obl_complete.
Proof.
  intros elements history Hadd Honly s t w [(from & value & to & Hto & Hdone) Hno].
  destruct (Hadd s t from value to Hdone) as (m & [Hfm Hmt] & Hin).
  assert (forall k, m + 1 <= k -> k <= w -> elements s k t) as Hstays.
  { apply (from_a_moment_on (fun k => k <= w -> elements s k t)).
    - intros _. rewrite (Hin t). left. reflexivity.
    - intros k Hk IH Hkw. destruct (classic (elements s (k + 1) t)) as [H | Hout]; [exact H | exfalso].
      apply Hno. destruct (proj2 (Honly s k t) (conj (IH ltac:(lia)) Hout)) as [[who Hc] | (m' & Hm' & who & Hb & _)].
      + exists k. split; [lia | exists who; exact Hc].
      + exists m'. split; [lia | exists who; left; exact Hb]. }
  apply Hstays; lia.
Qed.

(** Its parts can hold together: a run in which nothing happens, of sets with nothing in them, meets each. *)
Lemma whoIsAddedStays_Proofs_feasible : whoIsAddedStays_Obl_feasible.
Proof.
  exists (fun _ _ _ => False), (fun _ => Event_Stutter).
  split.
  { intros s x from value to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros s w y. split; [intros [_ H]; destruct H | intros [H _]; destruct H].
Qed.
