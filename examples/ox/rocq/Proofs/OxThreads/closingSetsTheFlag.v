Require Export FrFlowGen.OxThreads.closingSetsTheFlag.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing set the flag before it completed: the flag held true when that call of `set` completed, and stays
    set. *)
Lemma closingSetsTheFlag_Proofs_complete : closingSetsTheFlag_Obl_complete.
Proof.
  intros heldIn flag history _ Hstays Hitself Hset h from response to Hdone.
  destruct (Hitself h from response to Hdone) as (a & r1 & b & [Ha Hb] & Hcall).
  assert (flag (heldIn "ox.internal.ThreadHerd shutdownInProgress"%string h) b) as Hflag.
  { rewrite (Hset _ True a r1 b Hcall). exact I. }
  assert (b = to \/ b < to) as [<- | Hlt] by lia; [exact Hflag | apply (Hstays h b to); split; assumption].
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
  intros s b from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
