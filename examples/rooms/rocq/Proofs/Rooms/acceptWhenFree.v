Require Export FrFlowGen.Rooms.acceptWhenFree.Spec.
Require Export Proofs.Rooms.Lemmas.

(** A request is accepted exactly when its room is free: the code answers by the overlaps, and for bookings that
    end after they start that is whether the room is free. *)
Lemma acceptWhenFree_Proofs_impl : acceptWhenFree_Obl_impl.
Proof.
  intros h bookings request hw. rewrite (h bookings request).
  apply propositional_extensionality. symmetry. exact (Lemmas_free_noOverlap _ _ hw).
Qed.
