Require Export FrFlowGen.OxThreads.theMembershipCheckStaysOutOfHerds.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** What the thread calls while it is calling isOwnerOrHerdThread is contains of a set, or is called while that
    is pending: and that calls into no herd. *)
Lemma theMembershipCheckStaysOutOfHerds_Proofs_complete : theMembershipCheckStaysOutOfHerds_Obl_complete.
Proof.
  intros heldIn history _ Hlist Hjdk Hone h t h1 x.
  split; intros who from w Hpending Hcalled.
  all: destruct (called_under history _ who _ from _ w (Hone who)
    (fun made k Hmade => Hlist h t from made k (ex_intro _ who (conj (proj2 (proj1 Hpending)) Hmade)))
    Hpending Hcalled) as [(s & y & E) | (between & m & (s & y & ->) & Hunder)]; [discriminate E |].
  all: destruct (proj2 (Hjdk s s y) h1 x) as [Hclose Hremove].
  - exact (Hclose who m w Hunder Hcalled).
  - exact (Hremove who m w Hunder Hcalled).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
