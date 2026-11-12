Require Export FrFlowGen.Payments.neverCommitsAhead.Spec.

(** No step moves the committed offset but one that leaves the payment applied. The offset moves at the last
    step alone. By then the payment was authorised, so it is decided; and, if approved, it was posted. The other
    calls moved twice in between, and each move left the payment decided as it was and posted if it was: what
    the claim takes of them, read at each of their two moves. *)
Lemma neverCommitsAhead_Proofs_impl : neverCommitsAhead_Obl_impl.
Proof.
  intros; repeat (autounfold with frflow_defs in *; intros); cbv zeta in *;
  repeat (progress (frflow_props; frflow_simpl)); frflow_props.
  all: try frflow_close.
  all: right.
  all: match goal with H : forall move : PaymentHandler * PaymentHandler, _ |- _ =>
    try (pose proof (H _ (or_introl (or_introl eq_refl))));
    try (pose proof (H _ (or_intror (or_introl eq_refl))));
    try (pose proof (H _ (or_introl eq_refl)));
    clear H; cbn in * end.
  all: pose proof (h_authorisedIsRecorded (PaymentHandler_limits handler) p) as recorded.
  all: timeout 60 firstorder.
Qed.
