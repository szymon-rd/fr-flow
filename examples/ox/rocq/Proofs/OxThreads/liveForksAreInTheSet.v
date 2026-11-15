Require Export FrFlowGen.OxThreads.liveForksAreInTheSet.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The set of a herd is a set: what was added to it and not removed from it is in it. *)
Lemma liveForksAreInTheSet_Proofs_complete : liveForksAreInTheSet_Obl_complete.
Proof.
  intros elements heldIn steps Hstart Hatomic Hadd Hrem Honly h t w [Hfork Hleft].
  set (s := heldIn "ox.internal.ThreadHerd threads"%string h) in *.
  eapply (added_and_not_removed_is_in steps (elements s)).
  - exact Hstart.
  - intros x. exact (Hatomic s x).
  - intros x y. exact (Hadd s x y).
  - intros x y. exact (Hrem s x y).
  - intros a b y. exact (Honly s a b y).
  - exact Hfork.
  - exact Hleft.
Qed.
