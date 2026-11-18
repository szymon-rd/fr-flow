Require Export FrFlowGen.OxThreads.theClosingCheckStaysOutOfHerds.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** What a thread calls while it is calling the check is the check's own call, of `get`, or is called during
    that `get`: neither closes a herd nor removes from a set. *)
Lemma theClosingCheckStaysOutOfHerds_Proofs_complete : theClosingCheckStaysOutOfHerds_Obl_complete.
Proof.
  intros heldIn history _ Hget Hjdk Hone h h1 x.
  split; intros who from w Hpending Hcalled.
  all: destruct (called_under history _ who _ from _ w (Hone who)
    (fun made k Hmade => Hget h from made k (ex_intro _ who (conj (proj2 (proj1 Hpending)) Hmade)))
    Hpending Hcalled) as [(b & E) | (between & m & (b & ->) & Hunder)]; [discriminate E |].
  all: destruct (proj1 (proj1 (Hjdk b b b)) h1 x) as [Hclose Hremove].
  - exact (Hclose who m w Hunder Hcalled).
  - exact (Hremove who m w Hunder Hcalled).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
