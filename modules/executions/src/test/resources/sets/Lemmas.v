Require Export FrFlowGen.Sets.Domain.

(** In a run in which nothing happens, no call is made, and none completes. *)
Lemma nothing_called_at_rest c who w : ~ calledBy (fun _ => Event_Stutter) c who w.
Proof. intros [(inside & H) | (a & inside & spawns & H)]; discriminate. Qed.

Lemma nothing_completed_at_rest c who from a to : ~ completedBy (fun _ => Event_Stutter) c who from a to.
Proof. intros [[(inside & spawns & H) _] | [(inside & H) _]]; discriminate. Qed.

(** What holds at a moment, and at the next whenever it holds at one, holds from that moment on. *)
Lemma from_a_moment_on (P : Z -> Prop) (m : Z) :
  P m -> (forall k, m <= k -> P k -> P (k + 1)) -> forall k, m <= k -> P k.
Proof.
  intros Hm Hstep k Hk. replace k with (m + (k - m)) by lia.
  apply (natlike_ind (fun d => P (m + d))); [replace (m + 0) with m by lia; exact Hm | | lia].
  intros d Hd IH. replace (m + Z.succ d) with (m + d + 1) by lia. apply Hstep; [lia | exact IH].
Qed.
