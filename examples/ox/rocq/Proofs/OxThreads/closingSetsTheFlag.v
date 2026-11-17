Require Export FrFlowGen.OxThreads.closingSetsTheFlag.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing has set the flag: setting returns, and at a moment during the call the flag comes to hold true;
    from there it stays set. *)
Lemma closingSetsTheFlag_Proofs_complete : closingSetsTheFlag_Obl_complete.
Proof.
  intros heldIn flag history _ Hstays Hitself Hatomic Hreturns Hmade h from response to Hdone.
  destruct (Hitself h from response to Hdone) as (a & r1 & b & [Ha Hb] & Hcall).
  pose proof (Hreturns _ True a r1 b Hcall) as ->.
  destruct (Hatomic _ True a Value_Unit_ b Hcall) as (m & [Hm1 Hm2] & Hf).
  set (s := heldIn "ox.internal.ThreadHerd shutdownInProgress"%string h) in *.
  assert (flag s (m + 1)) as Hflag by (rewrite Hf; exact I).
  assert (m + 1 = to \/ m + 1 < to) as [<- | Hlt] by lia; [exact Hflag |].
  apply (Hstays h (m + 1) to). split; [split; [| exact Hlt] | exact Hflag].
  pose proof (completed_was_called _ _ _ _ _ _ Hdone) as Hc.
  refine (herd_constructed_later history h from _ _ (Hmade h from ltac:(unfold calledOn; eauto 14))). lia.
Qed.

(** Its parts can hold together: an execution in which nothing happens, of flags never set, meets each. *)
Lemma closingSetsTheFlag_Proofs_feasible : closingSetsTheFlag_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ _ => False), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h a b [_ H]. exact H. }
  split.
  { intros h from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s b from value to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s b from response to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
