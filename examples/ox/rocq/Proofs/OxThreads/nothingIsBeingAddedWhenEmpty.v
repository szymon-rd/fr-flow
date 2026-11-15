Require Export FrFlowGen.OxThreads.nothingIsBeingAddedWhenEmpty.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who is adding is calling startThread, so is inside the scope: not the owner, who has called closing, so a
    fork that has not left, which is in the set: the set is not empty. *)
Lemma nothingIsBeingAddedWhenEmpty_Proofs_complete : nothingIsBeingAddedWhenEmpty_Obl_complete.
Proof.
  intros heldIn history elements _ Hlive Hwho Hstay Hmade h t m [Hclosing Hempty] Hadd.
  assert (exists c, inside heldIn history c h m) as (c & Hin).
  { destruct Hadd as [[c Hc] | (a & Ha & c & Hb & Hn)].
    - destruct (Hwho h t c m (or_introl Hc)) as (code & Hp). exists c. apply (Hstay h code c m). right. exact Hp.
    - destruct (Hwho h t c m (or_intror (ex_intro _ a (conj Ha (conj Hb Hn))))) as (code & Hp).
      exists c. apply (Hstay h code c m). right. exact Hp. }
  destruct Hin as [[_ Hnot] | Hfork]; [exact (Hnot Hclosing) |].
  destruct Hclosing as (m1 & Hm1 & Hc1).
  apply (Hempty c). apply (Hlive h c m). split; [| exact Hfork].
  apply (made_later history h _ m1); [lia |].
  exact (Hmade h h m1 (or_intror (ex_intro (fun who => calledBy history _ who m1) _ Hc1))).
Qed.

(** Its parts can hold together: an execution in which nothing happens, of sets with nothing in them, meets
    each. *)
Lemma nothingIsBeingAddedWhenEmpty_Proofs_feasible : nothingIsBeingAddedWhenEmpty_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h t w [(m & by_ & ins & hs & _ & H) _]. discriminate H. }
  split.
  { intros h t c w [H | (a & _ & H & _)];
      [destruct (nothing_called_at_rest _ _ _ H) | destruct (nothing_begun_at_rest _ _ _ H)]. }
  split.
  { intros h code c w [H | (a & _ & H & _)];
      [destruct (nothing_called_at_rest _ _ _ H) | destruct (nothing_begun_at_rest _ _ _ H)]. }
  intros h code w [[who H] | [who H]]; destruct (nothing_called_at_rest _ _ _ H).
Qed.
