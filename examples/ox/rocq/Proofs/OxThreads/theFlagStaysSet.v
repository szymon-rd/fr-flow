Require Export FrFlowGen.OxThreads.theFlagStaysSet.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import Classical PropExtensionality.

(** Were the flag unset at a moment after it was set, there would be a moment at which it becomes unset. Only
    get and set are called on it, so that is during a call that sets it to false; that call is one closing
    makes itself; and closing sets it only to true. *)
Lemma theFlagStaysSet_Proofs_complete : theFlagStaysSet_Obl_complete.
Proof.
  intros flag heldIn history _ Hbecomes Hplain Honly Htrue h a b [[Hmade Hab] Hset].
  set (s := heldIn "ox.internal.ThreadHerd shutdownInProgress"%string h) in *.
  assert (forall k, a <= k -> k <= b -> flag s k) as Hall; [| apply Hall; lia].
  apply (from_a_moment_on (fun k => k <= b -> flag s k)); [intros _; exact Hset |].
  intros k Hk IH Hkb. destruct (classic (flag s (k + 1))) as [H | Hout]; [exact H | exfalso].
  assert (exists who m, calledBy history (Invocation_mk
    "java.util.concurrent.atomic.AtomicBoolean set scala.Boolean:scala.Unit"%string [s; Value_Bool_ False]) who m)
    as (who & m & Hcall).
  { destruct (Hbecomes s False k) as [[who Hc] | (m & _ & who & Hb & _)].
    - split; [split; [exact (Hplain h b Hmade) |] |].
      + intros E. rewrite E in IH. exact (IH ltac:(lia)).
      + apply propositional_extensionality. tauto.
    - exists who, k. exact Hc.
    - exists who, m. left. exact Hb. }
  destruct (Honly h False who m b (conj Hmade Hcall)) as (from & Hclosing & Hitself).
  exact (Htrue h False who from m (conj Hclosing Hitself)).
Qed.

(** Its parts can hold together: an execution in which nothing happens, of flags never set, meets each. *)
Lemma theFlagStaysSet_Proofs_feasible : theFlagStaysSet_Obl_feasible.
Proof.
  exists (fun _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros s v w [[_ H1] H2]. destruct (H1 H2). }
  split.
  { intros h w (x & who & from & to & _ & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h v c w b [_ H]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h v c from w [H _]. destruct (nothing_called_at_rest _ _ _ H).
Qed.
