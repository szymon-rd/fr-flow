Require Export FrFlowGen.OxThreads.whatIsInAHerdsSetWasMadeToRun.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** What is in the set is there by a call of add that returns; a call that adds to a herd's set is one startThread
    on the herd makes itself, and has not completed when it does. *)
Lemma whatIsInAHerdsSetWasMadeToRun_Proofs_complete : whatIsInAHerdsSetWasMadeToRun_Obl_complete.
Proof.
  intros elements heldIn history _ Hadded Honly Hwhile Hplain h x w b [Hcons Hin].
  destruct (Hadded (heldIn "ox.internal.ThreadHerd threads"%string h) x w (conj (Hplain h b Hcons) Hin))
    as (c & from & added & to & Hdone).
  destruct (Honly h x c from b (conj Hcons (completed_was_called _ _ _ _ _ _ Hdone)))
    as (code & from' & Hcalled & Hadds).
  exists code, to. exists c, from, added, to. split; [split; [lia | exact Hdone] |].
  exact (Hwhile h code c x from' from (conj Hcalled Hadds)).
Qed.

(** What it is from can hold: an execution in which nothing happens, of sets with nothing in them, meets each. *)
Lemma whatIsInAHerdsSetWasMadeToRun_Proofs_feasible : whatIsInAHerdsSetWasMadeToRun_Obl_feasible.
Proof.
  exists (fun _ _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros s x w [_ H]. destruct H. }
  split.
  { intros h t c w b [_ H]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h w Hready. destruct (nothing_ready_at_rest _ _ _ Hready).
Qed.
