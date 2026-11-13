Require Export FrFlowGen.Calendar.grantWhenFree.Spec.

(** The claim over moments, of the calendar's code, from the claim over start and end times: two bookings that end
    after they start are apart exactly when they do not overlap (rooms' own lemma), so the two claims give the code
    the same answer. The code is the definition FrFlow printed from the plain Scala (`Calendar.grantedCode`). *)
Lemma Calendar_apart_noOverlap (a b : Booking) :
  bookingsEndAfterStart a -> bookingsEndAfterStart b -> (apart a b <-> noOverlap a b).
Proof.
  unfold bookingsEndAfterStart, apart, noOverlap, shareNoMoment, covers. cbn. intros ha hb. split.
  - intros [hr | hs]; [left; left; exact hr |].
    destruct (Z_le_gt_dec (Booking_end_ a) (Booking_start b)) as [h1 | h1]; [left; right; exact h1 |].
    destruct (Z_le_gt_dec (Booking_end_ b) (Booking_start a)) as [h2 | h2]; [right; exact h2 |].
    exfalso. apply (hs (Z.max (Booking_start a) (Booking_start b))). lia.
  - intros [[hr | h1] | h2]; [left; exact hr | right; intros t; lia | right; intros t; lia].
Qed.

Lemma grantWhenFree_Proofs_impl : grantWhenFree_Obl_impl.
Proof.
  intros _ held hEnds request hRequest. unfold grantedCode, free. apply propositional_extensionality.
  split; intros H b hb; apply (Calendar_apart_noOverlap b request (hEnds b hb) hRequest); exact (H b hb).
Qed.
