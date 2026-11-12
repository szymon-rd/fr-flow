Require Export FrFlowGen.Rooms.neverOverlap.Spec.
Require Export Proofs.Rooms.Lemmas.

(** Booking keeps the bookings apart: a request is added only when it overlaps none of them, so it is apart from
    each, and those before it were apart already. *)
Lemma neverOverlap_Proofs_impl : neverOverlap_Obl_impl.
Proof.
  intros h bookings request [hw hp]. rewrite (h bookings request).
  destruct (classic (forall b, In b (storedBookings_booked bookings) -> noOverlap b request)) as [n | n].
  - rewrite (ite_true _ _ _ n). apply Lemmas_pairwise_snoc; [exact hp |].
    exact (proj2 (Lemmas_free_noOverlap _ _ hw) n).
  - rewrite (ite_false _ _ _ n). exact hp.
Qed.
