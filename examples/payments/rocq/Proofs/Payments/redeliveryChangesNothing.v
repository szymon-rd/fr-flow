Require Export FrFlowGen.Payments.redeliveryChangesNothing.Spec.

(** A payment handled again changes nothing. The card limits and the ledger each say so of their own step. The
    committed offset takes a case: where the first commit moved it past the payment, the second finds another
    offset and leaves it; where the first left it, so does the second. *)
Lemma redeliveryChangesNothing_Proofs_commit_twice
    (committed : ConsumerOffsets -> Z) (commit : ConsumerOffsets -> Z -> unit * ConsumerOffsets) :
  (forall o off, committed o = off -> committed (snd (commit o off)) = off + 1) ->
  (forall o off, committed o <> off -> snd (commit o off) = o) ->
  forall o off, snd (commit (snd (commit o off)) off) = snd (commit o off).
Proof.
  intros moves leaves o off. destruct (classic (committed o = off)) as [e | e].
  - apply leaves. rewrite (moves o off e). lia.
  - rewrite (leaves o off e). exact (leaves o off e).
Qed.

Lemma redeliveryChangesNothing_Proofs_impl : redeliveryChangesNothing_Obl_impl.
Proof.
  intros; repeat (autounfold with frflow_defs in *; intros); cbv zeta in *;
  repeat (progress (frflow_props; frflow_simpl)); frflow_props.
  all: try frflow_close.
  all: f_equal; first
    [ apply h_authoriseIsRepeatable | apply h_postIsRepeatable | reflexivity
    | apply (redeliveryChangesNothing_Proofs_commit_twice offsets_committed offsets_commit); assumption ].
Qed.
