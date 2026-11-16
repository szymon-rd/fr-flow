Require Export FrFlowGen.OxThreads.addingStopsOnceTheFlagIsSet.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** A call that adds to the herd's set is one a call of startThread on the herd makes itself; that call saw the
    flag unset at a moment during it, so before the flag was set, and it was made after the execution began. There
    are finitely many moments in between, and a call of startThread adds but once: so there is a last add. *)
Lemma addingStopsOnceTheFlagIsSet_Proofs_complete : addingStopsOnceTheFlagIsSet_Obl_complete.
Proof.
  intros flag heldIn history _ Hbegins Honce Hstays Hunset Honly h w0 [Hcons Hflag].
  pose (P := fun (s w : Z) => exists c code t,
    calledBy history
      (Invocation_mk "ox.internal.ThreadHerd startThread scala.Function0:scala.Unit"%string [h; code]) c s /\
    itselfMakes history
      (Invocation_mk "java.util.concurrent.ConcurrentHashMap$.KeySetView add java.lang.Object:scala.Boolean"%string
        [heldIn "ox.internal.ThreadHerd threads"%string h; t]) c s w).
  assert (forall s w w', P s w -> P s w' -> w = w') as Hone.
  { intros s w w' (c & code & t & Hc & Ha) (c' & code' & t' & Hc' & Ha').
    destruct (one_call_at_a_moment _ _ _ _ _ _ Hc Hc') as [E ->]. injection E as <-.
    exact (Honce h code c' s _ t w _ t' w' (conj (conj Hc Ha) Ha')). }
  destruct (bounded_over_a_window P 0 Hone (Z.to_nat (w0 + 1))) as [B HB].
  exists B. intros y w Hw [who Hadd].
  destruct (Honly h y who w (Z.max w w0)
    (conj (herd_constructed_later history h w0 (Z.max w w0) ltac:(lia) Hcons) Hadd))
    as (code & from & Hcalled & Hadds).
  destruct (Hunset h code who y from w (conj Hcalled (or_introl Hadds))) as (m & [Hfm Hmw] & Hnot).
  assert (m <= w0) as Hm.
  { destruct (Z_le_gt_dec m w0) as [Hle | Hgt]; [exact Hle | exfalso]. apply Hnot. apply (Hstays h w0 m).
    split; [split; [exact (herd_constructed_later history h w0 m ltac:(lia) Hcons) | lia] | exact Hflag]. }
  assert (0 <= from) as Hpos.
  { destruct (Z_lt_le_dec from 0) as [Hneg | Hok]; [exfalso; exact (Hbegins _ _ _ Hneg Hcalled) | exact Hok]. }
  pose proof (HB from w ltac:(lia)
    (ex_intro _ who (ex_intro _ code (ex_intro _ y (conj Hcalled Hadds))))) as Hlt.
  lia.
Qed.

(** What it is from can hold: an execution in which nothing happens, of flags never set, meets each. *)
Lemma addingStopsOnceTheFlagIsSet_Proofs_feasible : addingStopsOnceTheFlagIsSet_Obl_feasible.
Proof.
  exists (fun _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros made by_ w _ H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c from s t a s2 t2 a2 [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h a b [_ H]. destruct H. }
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h t c w b [_ H]. destruct (nothing_called_at_rest _ _ _ H).
Qed.
