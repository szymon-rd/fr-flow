Require Export FrFlowGen.OxThreads.theWalkUpStaysOutOfHerds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** What the thread calls while it is running the function is one of the four calls the function makes itself,
    none of which is closing or remove, or is called while one of those is pending. A scope's herd and parent
    call into no herd, nor does isOwnerOrHerdThread; and of the function applied again, later, the same holds:
    by induction on how long before the moment the function was applied. *)
Lemma theWalkUpStaysOutOfHerds_Proofs_complete : theWalkUpStaysOutOfHerds_Obl_complete.
Proof.
  intros heldIn history _ Hlist Hscope Hmember Hone g scope Hwalks h x.
  assert (forall n : nat, forall scope' who from w, (Z.to_nat (w - from) <= n)%nat ->
    (from < w /\ begun history (Invocation_mk L.Function_apply [g; scope']) who from) /\
      ~ overBy history who from w ->
    ~ calledBy history
        (Invocation_mk L.ThreadHerd_interruptAllAndJoinUntilCompleted [h]) who w /\
    ~ calledBy history (Invocation_mk
        L.KeySetView_remove
        [heldIn L.ThreadHerd_threads h; x]) who w) as Hall.
  { induction n as [| n IH]; intros scope' who from w Hn Hpending; [destruct Hpending as [[Hlt _] _]; lia |].
    split; intros Hcalled.
    all: destruct (called_under_later history _ who _ from _ w (Hone who)
      (fun made k Hmade =>
        Hlist g scope' Hwalks from made k (ex_intro _ who (conj (proj2 (proj1 Hpending)) Hmade)))
      Hpending Hcalled) as [Hown | (between & m & Hlater & Hallowed & Hunder)].
    1, 3: destruct Hown as [[[(s & E) | (s & E)] | (h2 & t & E)] | (s & E)]; discriminate E.
    all: destruct Hallowed as [[[(s & ->) | (s & ->)] | (h2 & t & ->)] | (s & ->)].
    - exact (proj1 (proj1 (Hscope s) h x) who m w Hunder Hcalled).
    - exact (proj1 (proj2 (Hscope s) h x) who m w Hunder Hcalled).
    - exact (proj1 (Hmember h2 t h x) who m w Hunder Hcalled).
    - exact (proj1 (IH s who m w ltac:(destruct Hunder as [[Hmw _] _]; lia) Hunder) Hcalled).
    - exact (proj2 (proj1 (Hscope s) h x) who m w Hunder Hcalled).
    - exact (proj2 (proj2 (Hscope s) h x) who m w Hunder Hcalled).
    - exact (proj2 (Hmember h2 t h x) who m w Hunder Hcalled).
    - exact (proj2 (IH s who m w ltac:(destruct Hunder as [[Hmw _] _]; lia) Hunder) Hcalled). }
  split; intros who from w Hpending.
  - exact (proj1 (Hall _ scope who from w (le_n _) Hpending)).
  - exact (proj2 (Hall _ scope who from w (le_n _) Hpending)).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
