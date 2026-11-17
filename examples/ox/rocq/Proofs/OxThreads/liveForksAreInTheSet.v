Require Export FrFlowGen.OxThreads.liveForksAreInTheSet.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The call that added the fork put it in the set at a moment during the call, so before `w`. From there to `w`
    it leaves at no moment: of a plain set it would leave only during a call that removes it, and none was made. *)
Lemma liveForksAreInTheSet_Proofs_complete : liveForksAreInTheSet_Obl_complete.
Proof.
  intros elements heldIn history _ Hadd Hleave Hplain h t w [Hmade [(from & value & to & Hto & Hdone) Hleft]].
  set (s := heldIn "ox.internal.ThreadHerd threads"%string h) in *.
  destruct (Hadd s t from value to Hdone) as (m & [Hfm Hmt] & Hin).
  assert (forall k, m + 1 <= k -> k <= w -> elements s k t) as Hstays.
  { apply (from_a_moment_on (fun k => k <= w -> elements s k t)).
    - intros _. rewrite (Hin t). left. reflexivity.
    - intros k Hk IH Hkw. destruct (classic (elements s (k + 1) t)) as [H | Hout]; [exact H | exfalso].
      apply Hleft.
      destruct (Hleave s t k (conj (conj (Hplain h w Hmade) (IH ltac:(lia))) Hout))
        as [[who Hc] | (m' & Hm' & who & Hb & _)].
      + exists k. split; [lia | exists who; exact Hc].
      + exists m'. split; [lia | exists who; left; exact Hb]. }
  apply Hstays; lia.
Qed.

(** Its parts can hold together: a run in which nothing happens, of sets with nothing in them, meets each. *)
Lemma liveForksAreInTheSet_Proofs_feasible : liveForksAreInTheSet_Obl_feasible.
Proof.
  exists (fun _ _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros s x from value to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s x w [[_ H] _]. destruct H. }
  intros h w Hready. destruct (nothing_ready_at_rest _ _ _ Hready).
Qed.
