Require Export FrFlowGen.OxThreads.whatAHerdsCodeCallsOfASet.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Each method of a herd, and the function startThread hands the factory, has its list of the calls it makes
    itself, proven of its tree. Of those, the ones of a key set's methods are these five. *)
Lemma whatAHerdsCodeCallsOfASet_Proofs_complete : whatAHerdsCodeCallsOfASet_Obl_complete.
Proof.
  intros history heldIn _ Hclosing Howner Hmember Hfork Hstart Hcheck Htree h c i made w
    [[Hby Hmk] (method & taking & -> & Hof)].
  destruct Hby as [[[[[[(x & Hb) | Hb] | (x & Hb)] | Hb] | Hb] | Hb] | (r & Hhand & Hrun)].
  - destruct (Hstart h x i _ w (ex_intro _ c (conj Hb Hmk)))
      as [[[[H | H] | (f & r & H)] | (s & t & H)] | (t & H)]; inversion H; subst.
    1, 2, 3, 5: exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
    left; left; left. split; [exists x; exact (begun_is_called _ _ _ _ Hb) | exists s, t; reflexivity].
  - destruct (Hclosing h i _ w (ex_intro _ c (conj Hb Hmk))) as [[[H | (b & H)] | (s & H)] | (s & f & H)];
      inversion H; subst.
    1, 2: exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
    + left; left; right. split; [exact (begun_is_called _ _ _ _ Hb) | left; exists s; reflexivity].
    + left; left; right. split; [exact (begun_is_called _ _ _ _ Hb) | right; exists s, f; reflexivity].
  - destruct (Hmember h x i _ w (ex_intro _ c (conj Hb Hmk))) as (s & y & H). inversion H; subst.
    left; right. split; [exists x; exact (begun_is_called _ _ _ _ Hb) | exists s, y; reflexivity].
  - destruct (Hcheck h i _ w (ex_intro _ c (conj Hb Hmk))) as (b & H). inversion H; subst.
    exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
  - destruct (Htree h i _ w (ex_intro _ c (conj Hb Hmk))) as [[[H | H] | (t & H)] | (f & scope & H)];
      inversion H; subst; exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
  - pose proof (Howner h i _ w (ex_intro _ c (conj Hb Hmk))) as H. inversion H; subst.
    exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
  - destruct (Hfork h r c i _ w (conj (conj Hhand Hrun) Hmk)) as [[[(code & H) | H] | (s & t & H)] | (x & H)];
      inversion H; subst.
    1, 2, 4: exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
    right. split; [exists r; split; assumption | exists s, t; reflexivity].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma whatAHerdsCodeCallsOfASet_Proofs_feasible : whatAHerdsCodeCallsOfASet_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter), (fun _ x => x).
  split; [exact rest_runs |].
  split.
  { intros h from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h t from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h r c i made w [[_ H] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros h from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  intros h from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H).
Qed.
