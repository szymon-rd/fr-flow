Require Export FrFlowGen.OxThreads.onlyClosingSetsTheFlag.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** A call that sets the herd's flag is made by one of the herd's methods, itself; of those only closing sets
    an atomic boolean. *)
Lemma onlyClosingSetsTheFlag_Proofs_complete : onlyClosingSetsTheFlag_Obl_complete.
Proof.
  intros heldIn history _ Hkeeps Hmethods h v c w b [Hconstructed Hcalled].
  destruct (Hkeeps h b Hconstructed _ _ c w Hcalled) as (i & Hmk & [Hby | []]).
  lazymatch type of Hmk with itselfMakes _ ?made _ _ _ =>
    destruct (Hmethods h c i made w) as [(flag & E) | [Hclosing _]] end.
  { split; [split; assumption |]. eexists _, _. split; [reflexivity |].
    repeat (first [right; reflexivity | left]). }
  - discriminate E.
  - exists i. split; assumption.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma onlyClosingSetsTheFlag_Proofs_feasible : onlyClosingSetsTheFlag_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h w (x & who & from & to & _ & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h c i made w [[_ H] _]. destruct H as [H | (a & spawns & H)]; discriminate H.
Qed.
