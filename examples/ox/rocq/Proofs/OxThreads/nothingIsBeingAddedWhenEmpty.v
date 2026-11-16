Require Export FrFlowGen.OxThreads.nothingIsBeingAddedWhenEmpty.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who is adding is calling startThread, so is inside the scope: not the owner, who has called closing, so a
    fork that has not left, which is in the set: the set is not empty. *)
Lemma nothingIsBeingAddedWhenEmpty_Proofs_complete : nothingIsBeingAddedWhenEmpty_Obl_complete.
Proof.
  intros heldIn history elements _ Hlive Hwho Hstay Hmade h t m [Hclosing Hempty] Hadd.
  pose proof Hclosing as (m1 & Hm1 & Hc1).
  pose proof (herd_constructed_later history h m1 m ltac:(lia)
    (Hmade h m1 ltac:(unfold calledOn; eauto 14))) as Hherd.
  assert (exists c, inside heldIn history c h m) as (c & Hin).
  { destruct Hadd as [[c Hc] | (a & Ha & c & Hb & Hn)].
    - destruct (Hwho h t c m m (conj Hherd (or_introl Hc))) as (code & Hp). exists c.
      apply (Hstay h code c m). right. exact Hp.
    - destruct (Hwho h t c m m (conj Hherd (or_intror (ex_intro _ a (conj Ha (conj Hb Hn)))))) as (code & Hp).
      exists c. apply (Hstay h code c m). right. exact Hp. }
  destruct Hin as [[_ Hnot] | Hfork]; [exact (Hnot Hclosing) |].
  apply (Hempty c). apply (Hlive h c m). split; [exact Hherd | exact Hfork].
Qed.

(** Its parts can hold together: an execution in which nothing happens, of sets with nothing in them, meets
    each. *)
Lemma nothingIsBeingAddedWhenEmpty_Proofs_feasible : nothingIsBeingAddedWhenEmpty_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h t w [(x & who & from & to & _ & H) _]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h t c w b [_ [H | (a & _ & H & _)]];
      [destruct (nothing_called_at_rest _ _ _ H) | destruct (nothing_begun_at_rest _ _ _ H)]. }
  split.
  { intros h code c w [H | (a & _ & H & _)];
      [destruct (nothing_called_at_rest _ _ _ H) | destruct (nothing_begun_at_rest _ _ _ H)]. }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
