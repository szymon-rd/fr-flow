Require Export FrFlowGen.OxThreads.theFlagStaysSet.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import Classical PropExtensionality.

(** Were the flag unset after it was set, a call would have set it to false; that call would be one closing
    makes itself; and closing sets it only to true. *)
Lemma theFlagStaysSet_Proofs_complete : theFlagStaysSet_Obl_complete.
Proof.
  intros flag heldIn history _ Hchanges Honly Htrue h a b [Hab Hset].
  destruct (classic (flag (heldIn "ox.internal.ThreadHerd shutdownInProgress"%string h) b)) as [Hb | Hb];
    [exact Hb | exfalso].
  destruct (Hchanges (heldIn "ox.internal.ThreadHerd shutdownInProgress"%string h) False a b)
    as (m & _ & who & Hcall).
  { split; [split; [exact Hab |] |].
    - intros E. rewrite E in Hset. exact Hset.
    - apply propositional_extensionality. tauto. }
  destruct (Honly h False who m Hcall) as (from & Hclosing & Hitself).
  exact (Htrue h False who from m (conj Hclosing Hitself)).
Qed.

(** Its parts can hold together: an execution in which nothing happens, of flags never set, meets each. *)
Lemma theFlagStaysSet_Proofs_feasible : theFlagStaysSet_Obl_feasible.
Proof.
  exists (fun _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros s v a b [[_ H1] H2]. destruct (H1 H2). }
  split.
  { intros h v c w H. destruct (nothing_called_at_rest _ _ _ H). }
  intros h v c from w [H _]. destruct (nothing_called_at_rest _ _ _ H).
Qed.
