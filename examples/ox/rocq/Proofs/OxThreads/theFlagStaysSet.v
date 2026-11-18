Require Export FrFlowGen.OxThreads.theFlagStaysSet.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import Classical PropExtensionality.

(** Were the flag unset at a moment after it was set, there would be a moment at which it becomes unset. Only
    get and set are called on it, so that is during a call that sets it to false; that call is one closing
    makes itself; and closing sets it only to true. *)
Lemma theFlagStaysSet_Proofs_complete : theFlagStaysSet_Obl_complete.
Proof.
  intros flag heldIn history _ Hbecomes Hplain Honly Htrue h a b [[Hmade Hab] Hset].
  set (s := heldIn L.ThreadHerd_shutdownInProgress h) in *.
  assert (forall k, a <= k -> k <= b -> flag s k) as Hall; [| apply Hall; lia].
  apply (from_a_moment_on (fun k => k <= b -> flag s k)); [intros _; exact Hset |].
  intros k Hk IH Hkb. destruct (classic (flag s (k + 1))) as [H | Hout]; [exact H | exfalso].
  assert (exists who m, calledBy history (Invocation_mk
    L.AtomicBoolean_set [s; Value_Bool_ False]) who m)
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
