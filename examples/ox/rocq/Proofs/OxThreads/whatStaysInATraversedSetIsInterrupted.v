Require Export FrFlowGen.OxThreads.whatStaysInATraversedSetIsInterrupted.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** With no call adding to the set in progress from the traversal's call on, nothing enters it: what is in it
    after the traversal was in it all through. The traversal returned, so it applied its function to the thread;
    the thread was made to run code, so that call was responded to; and once it has completed, the thread has
    been interrupted. *)
Lemma whatStaysInATraversedSetIsInterrupted_Proofs_complete : whatStaysInATraversedSetIsInterrupted_Obl_complete.
Proof.
  intros elements heldIn history _ Hrespond Hmade Henters Hreaches Hinterrupt Hreturn Hplain h x a b w made
    [[[Hcons Htrav] Hbw] Hin].
  destruct Htrav as (f & from & r & [[Hcalled Hmakes] Hdone] & Hnone).
  set (S := heldIn "ox.internal.ThreadHerd threads"%string h) in *.
  set (o := heldIn "ox.internal.ThreadHerd herdOwner"%string h) in *.
  pose proof (Hreturn h f from a b r (conj (conj Hcalled Hmakes) Hdone)) as Er. rewrite Er in Hdone.
  (* the thread was in the set from the traversal's call on *)
  assert (forall d, 0 <= d -> d <= w - a -> elements S (w - d) x) as Hback.
  { apply (natlike_ind (fun d => d <= w - a -> elements S (w - d) x)).
    - intros _. replace (w - 0) with w by lia. exact Hin.
    - intros d Hd IH Hle.
      destruct (Classical_Prop.classic (elements S (w - Z.succ d) x)) as [Hyes | Hno]; [exact Hyes | exfalso].
      apply (Hnone x (w - Z.succ d) ltac:(lia)). apply (Henters S x (w - Z.succ d)).
      split; [split; [exact (Hplain h made Hcons) | exact Hno] |].
      replace (w - Z.succ d + 1) with (w - d) by lia. apply IH. lia. }
  assert (forall k, a <= k <= w -> elements S k x) as Hall.
  { intros k Hk. replace k with (w - (w - k)) by lia. apply Hback; lia. }
  (* so the traversal applied its function to it *)
  assert (forall k, a <= k /\ k <= b -> elements S k x) as Hthrough by (intros k Hk; apply Hall; lia).
  destruct (Hreaches S f o x a b (conj Hdone Hthrough)) as (m & Ham & Hm).
  assert (calledBy history
    (Invocation_mk "java.util.function.Consumer accept java.lang.Object:scala.Unit"%string [f; x]) o m) as Hacc.
  { destruct Hm as [E | (r0 & sp & E)]; [left; exists (Some a); exact E |].
    right. exists r0, (Some a), sp. exact E. }
  assert (traversedWith heldIn history f h m) as Hwith.
  { exists from, a. split; [split; [exact Ham | exact Hcalled] | exact Hmakes]. }
  (* which was responded to, the thread being one made to run code *)
  destruct (Hmade h x w made (conj Hcons Hin)) as (code & mk & Hrun).
  destruct (Hrespond h f x o m code mk (conj (conj Hwith Hacc) Hrun)) as [Hbegun (to & k & resp & sp & Hk & Hresp)].
  (* and the thread has been interrupted by then *)
  destruct (Hinterrupt h f x o m resp (k + 1)) as (ifrom & value & ito & Hito & who & Hint).
  { split; [exact Hwith |]. right. split; [exact Hbegun |]. exists sp. replace (k + 1 - 1) with k by lia. exact Hresp. }
  exists (k + 1), ifrom, value, ito. split; [exact Hito | exists who; exact Hint].
Qed.

(** What it is from can hold: an execution in which nothing happens, of sets that hold nothing, meets each. *)
Lemma whatStaysInATraversedSetIsInterrupted_Proofs_feasible : whatStaysInATraversedSetIsInterrupted_Obl_feasible.
Proof.
  exists (fun _ _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h f x c k code made [[_ H] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h x w b [_ H]. destruct H. }
  split.
  { intros s x w [_ H]. destruct H. }
  split.
  { intros s f c x from to [H _]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h f x c k r b [_ H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h f from a b r [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h w (x & by_ & from & to & _ & H). destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
