Require Export FrFlowGen.Rooms.bookWhenFree.Spec.
Require Export Proofs.Rooms.Lemmas.

(** The bookings after a request are those before it, with the request added if its room is free: the code adds
    it when it overlaps none, which for bookings that end after they start is when the room is free. *)
Lemma bookWhenFree_Proofs_impl : bookWhenFree_Obl_impl.
Proof.
  intros h bookings request hw. rewrite (h bookings request). unfold addedIfFree.
  destruct (classic (free (storedBookings_booked bookings) request)) as [f | f].
  - rewrite (ite_true _ _ _ f). apply ite_true. exact (proj1 (Lemmas_free_noOverlap _ _ hw) f).
  - rewrite (ite_false _ _ _ f). apply ite_false. intro n. exact (f (proj2 (Lemmas_free_noOverlap _ _ hw) n)).
Qed.
