Require Export FrFlowGen.OxThreads.addingEndsOnceTheFlagIsSet.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** From some moment on no call that adds is made. Those made before were made after the execution began: at
    finitely many moments, one call at a moment, and each is responded to. So there is a moment by which each is
    over. *)
Lemma addingEndsOnceTheFlagIsSet_Proofs_complete : addingEndsOnceTheFlagIsSet_Obl_complete.
Proof.
  intros flag heldIn history _ Hstops Hresponds Hbegins h w0 Hset.
  destruct (Hstops h w0 Hset) as [L HL].
  pose (Q := fun (s e : Z) => forall who y, begun history
    (Invocation_mk L.KeySetView_add
      [heldIn L.ThreadHerd_threads h; y]) who s -> overBy history who s e).
  destruct (all_over_a_window Q 0) with (n := Z.to_nat L) as [E HE].
  { intros s e e' Hq Hle who y Hb. exact (over_later history who s e e' Hle (Hq who y Hb)). }
  { intros s. destruct (Classical_Prop.classic (exists who y, begun history
      (Invocation_mk L.KeySetView_add
        [heldIn L.ThreadHerd_threads h; y]) who s)) as [(who0 & y0 & Hb0) | Hnone].
    - destruct (Hresponds _ y0 who0 s (conj Hb0 I)) as [e He]. exists e. intros who y Hb.
      destruct (one_call_at_a_moment _ _ _ _ _ _ (or_introl Hb) (or_introl Hb0)) as [_ ->]. exact He.
    - exists 0. intros who y Hb. destruct Hnone. exists who, y. exact Hb. }
  exists (Z.max L E). intros y w Hw [[who Hcalled] | (m & Hm & who & Hb & Hpending)].
  - exact (HL y w ltac:(lia) (ex_intro _ who Hcalled)).
  - destruct (Z_lt_le_dec m L) as [Hlt | Hge]; [| exact (HL y m Hge (ex_intro _ who (or_introl Hb)))].
    destruct (Z_lt_le_dec m 0) as [Hneg | Hpos]; [exact (Hbegins _ _ m Hneg (or_introl Hb)) |].
    apply Hpending. exact (over_later history who m E w ltac:(lia) (HE m ltac:(lia) who y Hb)).
Qed.

(** What it is from can hold: an execution in which nothing happens, of flags never set, meets each. *)
