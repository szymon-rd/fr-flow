Require Export FrFlowGen.OxThreads.aHerdsSetEmptiesOnceTraversed.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** What is in the set was added by a call, made before the traversal's and after the execution began: at one of
    finitely many moments, one call at a moment. A thread so added is out of the set by the traversal's end, or
    it has been interrupted and is one made to run code, so it leaves for good: by some moment each is out, and
    nothing is in the set. The calls that remove, made before that moment, are finitely many too, and each is
    responded to: by a later moment each is over. *)
Lemma aHerdsSetEmptiesOnceTraversed_Proofs_complete : aHerdsSetEmptiesOnceTraversed_Obl_complete.
Proof.
  intros heldIn history elements _ Hmade Hadded Hbegins Hresponds Hinterrupted Hleaves Hplain h made Hcons
    f from a r b [[[Hcalled Hmakes] Hdone] Hnone].
  set (S := heldIn L.ThreadHerd_threads h) in *.
  assert (traversedWithNoneAdding heldIn history h a b) as Htrav.
  { exists f, from, r. split; [split; [split; [exact Hcalled | exact Hmakes] | exact Hdone] | exact Hnone]. }
  pose (Q := fun (s e : Z) => forall who y, calledBy history (Invocation_mk
    L.KeySetView_add [S; y]) who s ->
    forall w, e <= w -> ~ elements S w y).
  destruct (all_over_a_window Q 0) with (n := Z.to_nat a) as [E HE].
  { intros s e e' Hq Hle who y Hc w Hw. apply (Hq who y Hc w). lia. }
  { intros s. destruct (Classical_Prop.classic (exists who y, calledBy history (Invocation_mk
      L.KeySetView_add [S; y]) who s))
      as [(who0 & y0 & Hc0) | Hnocall].
    - destruct (Classical_Prop.classic (exists w, b <= w /\ elements S w y0)) as [(w0 & Hw0 & Hin0) | Hout].
      + pose proof (Hinterrupted h y0 a b w0 made (conj (conj (conj Hcons Htrav) Hw0) Hin0)) as Hint.
        destruct (Hmade h y0 w0 made (conj Hcons Hin0)) as (code & mk & Hrun).
        destruct (Hleaves h y0 code mk (conj Hrun Hint)) as [e He]. exists e. intros who y Hc.
        destruct (one_call_at_a_moment _ _ _ _ _ _ Hc Hc0) as [Einv _]. injection Einv as ->. exact He.
      + exists b. intros who y Hc w Hw Hin.
        destruct (one_call_at_a_moment _ _ _ _ _ _ Hc Hc0) as [Einv _]. injection Einv as ->.
        apply Hout. exists w. split; assumption.
    - exists 0. intros who y Hc. destruct Hnocall. exists who, y. exact Hc. }
  set (empty := Z.max E b).
  assert (forall y w, empty <= w -> ~ elements S w y) as Hempty.
  { intros y w Hw Hin.
    destruct (Hadded S y w (conj (Hplain h made Hcons) Hin)) as (c & afrom & added & ato & Hadd).
    pose proof (completed_was_called _ _ _ _ _ _ Hadd) as Hc.
    assert (afrom < a) as Hlt.
    { destruct (Z_lt_le_dec afrom a) as [Hl | Hge]; [exact Hl | exfalso].
      apply (Hnone y afrom Hge). left. exists c. exact Hc. }
    assert (0 <= afrom) as Hpos.
    { destruct (Z_lt_le_dec afrom 0) as [Hneg | Hok]; [exfalso; exact (Hbegins _ _ _ Hneg Hc) | exact Hok]. }
    exact (HE afrom ltac:(lia) c y Hc w ltac:(lia) Hin). }
  pose (R := fun (s e : Z) => forall who y, begun history (Invocation_mk
    L.KeySetView_remove [S; y]) who s ->
    overBy history who s e).
  destruct (all_over_a_window R 0) with (n := Z.to_nat empty) as [E1 HE1].
  { intros s e e' Hr Hle who y Hb. exact (over_later history who s e e' Hle (Hr who y Hb)). }
  { intros s. destruct (Classical_Prop.classic (exists who y, begun history (Invocation_mk
      L.KeySetView_remove [S; y]) who s))
      as [(who0 & y0 & Hb0) | Hno].
    - destruct (Hresponds S y0 who0 s (conj Hb0 I)) as [e He]. exists e. intros who y Hb.
      destruct (one_call_at_a_moment _ _ _ _ _ _ (or_introl Hb) (or_introl Hb0)) as [_ ->]. exact He.
    - exists 0. intros who y Hb. destruct Hno. exists who, y. exact Hb. }
  exists empty, (Z.max empty E1). split; [lia |]. intros y w. split; [exact (Hempty y w) |].
  intros Hw [Hlt (who & Hb & Hnot)]. apply Hnot.
  destruct (Z_lt_le_dec w 0) as [Hneg | Hpos]; [exfalso; exact (Hbegins _ _ w Hneg (or_introl Hb)) |].
  exact (over_later history who w E1 (Z.max empty E1) ltac:(lia) (HE1 w ltac:(lia) who y Hb)).
Qed.

(** What it is from can hold: an execution in which nothing happens, of sets that hold nothing, meets each. *)
