Require Export FrFlowGen.OxThreads.onlyAForkFunctionRemoves.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** A call that removes from the herd's set is made by a method of the herd, or by a function startThread handed
    the factory, itself; of those only that function calls remove of a key set. *)
Lemma onlyAForkFunctionRemoves_Proofs_complete : onlyAForkFunctionRemoves_Obl_complete.
Proof.
  intros heldIn history _ Hkeeps Hcalls h t c w b [Hconstructed Hcalled].
  destruct (Hkeeps h b Hconstructed _ _ c w Hcalled) as (i & Hmk & Hby).
  lazymatch type of Hmk with itselfMakes _ ?made _ _ _ =>
    destruct (Hcalls h c i made w)
      as [[[[_ (s & t' & E)] | [_ [(s & E) | (s & f & E)]]] | [_ (s & y & E)]] | [(r & Hhand & Hrun) _]] end.
  { split; [split; assumption |]. eexists _, _. split; [reflexivity |].
    repeat (first [right; reflexivity | left]). }
  all: try discriminate E.
  exists r, i. split; [split; assumption | assumption].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
