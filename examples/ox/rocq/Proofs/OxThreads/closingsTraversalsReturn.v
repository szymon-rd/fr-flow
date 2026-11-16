Require Export FrFlowGen.OxThreads.closingsTraversalsReturn.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** A traversal closing makes is given a function, no null: so it returns, or throws what a call of that
    function threw during it. Such a call is of a function closing passed to a traversal, which returns. *)
Lemma closingsTraversalsReturn_Proofs_complete : closingsTraversalsReturn_Obl_complete.
Proof.
  intros heldIn history _ Htraversal Hfunction Hreturn h f from a b r [[Hcalled Hmakes] Hdone].
  assert (forall k, a < k -> traversedWith heldIn history f h k) as Hwith.
  { intros k Hk. exists from, a. split; [split; [exact Hk | exact Hcalled] | exact Hmakes]. }
  destruct (Htraversal _ f _ (Hfunction h f (a + 1) (Hwith (a + 1) ltac:(lia))) a r b Hdone)
    as [-> | (x & e & a' & b' & [[[[Ha' _] ->] _] Hthrew])]; [reflexivity |].
  pose proof (Hreturn h f x _ a' _ b' (conj (Hwith a' Ha') Hthrew)) as E. discriminate E.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma closingsTraversalsReturn_Proofs_feasible : closingsTraversalsReturn_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros s f c _ from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h f w (from & a & [[_ H] _]). destruct (nothing_called_at_rest _ _ _ H). }
  intros h f x c k r b [_ H]. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
