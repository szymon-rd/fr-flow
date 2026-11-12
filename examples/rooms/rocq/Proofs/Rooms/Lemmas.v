Require Export FrFlowGen.Rooms.Domain.

(** What the proofs of rooms share: the purpose speaks of the moments two bookings cover, the code of when each
    starts and ends. For bookings that end after they start, the two say the same. *)

(** Two bookings that end after they start share no moment exactly when one ends by the time the other starts. *)
Lemma Lemmas_apart_noOverlap (a b : Booking) :
  endsAfterStart a -> endsAfterStart b -> (apart a b <-> noOverlap a b).
Proof.
  unfold endsAfterStart, apart, noOverlap, shareNoMoment, covers. cbn. intros ha hb. split.
  - intros [hr | hs]; [left; left; exact hr |].
    destruct (classic (Booking_room a = Booking_room b)) as [e | e]; [| left; left; exact e].
    destruct (Z_le_gt_dec (Booking_end_ a) (Booking_start b)) as [h1 | h1]; [left; right; exact h1 |].
    destruct (Z_le_gt_dec (Booking_end_ b) (Booking_start a)) as [h2 | h2]; [right; exact h2 |].
    exfalso. apply (hs (Z.max (Booking_start a) (Booking_start b))). lia.
  - intros [[hr | h1] | h2]; [left; exact hr | right; intros t; lia | right; intros t; lia].
Qed.

(** A room is free for a request exactly when the request overlaps none of the bookings. *)
Lemma Lemmas_free_noOverlap (held : list Booking) (request : Booking) :
  wellFormed held request -> (free held request <-> forall b, In b held -> noOverlap b request).
Proof.
  unfold wellFormed, free. intros [hh hr].
  split; intros h b hb; apply (Lemmas_apart_noOverlap b request (hh b hb) hr); exact (h b hb).
Qed.

(** What holds of each two of a list holds of each two with one more at the end, when it holds of each and it. *)
Lemma Lemmas_pairwise_snoc {A : Type} (p : A -> A -> Prop) (xs : list A) (x : A) :
  List_Pairwise p xs -> (forall y, In y xs -> p y x) -> List_Pairwise p (xs ++ [x]).
Proof.
  unfold List_Pairwise. induction 1 as [| y ys hy hrest ih]; intros hx; cbn.
  - constructor; constructor.
  - constructor.
    + apply Forall_app. split; [exact hy | constructor; [apply hx; left; reflexivity | constructor]].
    + apply ih. intros z hz. apply hx. right. exact hz.
Qed.
