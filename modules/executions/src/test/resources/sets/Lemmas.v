Require Export FrFlowGen.Sets.Domain.

(** In a run in which nothing happens, no call is made, and none completes. *)
Lemma nothing_called_at_rest c who w : ~ calledBy (fun _ => Event_Stutter) c who w.
Proof. intros [(inside & H) | (a & inside & spawns & H)]; discriminate. Qed.

Lemma nothing_completed_at_rest c who from a to : ~ completedBy (fun _ => Event_Stutter) c who from a to.
Proof. intros [[(inside & spawns & H) _] | [(inside & H) _]]; discriminate. Qed.
