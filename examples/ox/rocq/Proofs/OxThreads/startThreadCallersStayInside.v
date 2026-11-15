Require Export FrFlowGen.OxThreads.startThreadCallersStayInside.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** A caller of startThread is inside when it calls, and does nothing during the call that would take it out:
    it neither closes a herd nor removes from a herd's set, and no other thread removes it. *)
Lemma startThreadCallersStayInside_Proofs_complete : startThreadCallersStayInside_Obl_complete.
Proof.
  intros history heldIn _ Hinside Hneither Honly h code c w [Hcalled | (m & Hm & Hbegun & Hpending)].
  { exact (Hinside h code c w Hcalled). }
  assert (forall k, m <= k -> k <= w -> inside heldIn history c h k) as Hall; [| apply Hall; lia].
  apply (from_a_moment_on (fun k => k <= w -> inside heldIn history c h k)).
  { intros _. apply (Hinside h code c m). apply begun_is_called. exact Hbegun. }
  intros k Hk IH Hkw. specialize (IH ltac:(lia)).
  assert (~ calledBy history (Invocation_mk
      "ox.internal.ThreadHerd interruptAllAndJoinUntilCompleted :scala.Unit"%string [h]) c k /\
    ~ calledBy history (Invocation_mk
      "java.util.concurrent.ConcurrentHashMap$.KeySetView remove java.lang.Object:scala.Boolean"%string
      [heldIn "ox.internal.ThreadHerd threads"%string h; c]) c k) as [Hnoclose Hnoleave].
  { destruct (Z.eq_dec k m) as [-> | Hne].
    - split; intros Hc;
        destruct (one_call_at_a_moment history _ _ _ _ m Hc (begun_is_called _ _ _ _ Hbegun)) as [E _];
        discriminate E.
    - assert ((m < k /\ begun history (Invocation_mk
          "ox.internal.ThreadHerd startThread scala.Function0:scala.Unit"%string [h; code]) c m) /\
        ~ overBy history c m k) as Hp.
      { split; [split; [lia | exact Hbegun] |]. intros Hover. apply Hpending.
        apply (over_later history c m k w); [lia | exact Hover]. }
      destruct (Hneither h code h c) as [Hclose Hremove]. split; [exact (Hclose c m k Hp) | exact (Hremove c m k Hp)]. }
  destruct IH as [[Hown Hnot] | [Hfork Hstays]].
  - left. split; [exact Hown |]. intros (m1 & Hm1 & Hc1).
    assert (m1 < k \/ m1 = k) as [Hlt | ->] by lia.
    + apply Hnot. exists m1. split; [exact Hlt | exact Hc1].
    + apply Hnoclose. rewrite Hown. exact Hc1.
  - right. split.
    + destruct Hfork as (a & value & to & Hto & Hadd). exists a, value, to. split; [lia | exact Hadd].
    + intros (m1 & Hm1 & who & Hrem). assert (m1 < k \/ m1 = k) as [Hlt | ->] by lia.
      * apply Hstays. exists m1. split; [exact Hlt | exists who; exact Hrem].
      * pose proof (Honly h c who k Hrem) as ->. exact (Hnoleave Hrem).
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
Lemma startThreadCallersStayInside_Proofs_feasible : startThreadCallersStayInside_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter), (fun _ x => x).
  split; [exact rest_runs |].
  split.
  { intros h code c w H. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code h1 x. split; intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  intros h t c w H. destruct (nothing_called_at_rest _ _ _ H).
Qed.
