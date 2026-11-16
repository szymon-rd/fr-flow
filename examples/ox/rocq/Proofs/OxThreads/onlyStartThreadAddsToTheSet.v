Require Export FrFlowGen.OxThreads.onlyStartThreadAddsToTheSet.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** A call that adds to the herd's set is made by a method of the herd, or by a function startThread handed the
    factory, itself; of those only startThread calls add of a key set. *)
Lemma onlyStartThreadAddsToTheSet_Proofs_complete : onlyStartThreadAddsToTheSet_Obl_complete.
Proof.
  intros heldIn history _ Hkeeps Hcalls h t c w b [Hconstructed Hcalled].
  destruct (Hkeeps h b Hconstructed _ _ c w Hcalled) as (i & Hmk & Hby).
  lazymatch type of Hmk with itselfMakes _ ?made _ _ _ =>
    destruct (Hcalls h c i made w)
      as [[[[(code & Hstart) _] | [_ [(s & E) | (s & f & E)]]] | [_ (s & y & E)]] | [_ (s & t' & E)]] end.
  { split; [split; assumption |]. eexists _, _. split; [reflexivity |].
    repeat (first [right; reflexivity | left]). }
  all: try discriminate E.
  exists code, i. split; assumption.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma onlyStartThreadAddsToTheSet_Proofs_feasible : onlyStartThreadAddsToTheSet_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h w (x & who & from & to & _ & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h c i made w [[_ H] _]. destruct H as [H | (a & spawns & H)]; discriminate H.
Qed.
