Require Export FrFlowGen.OxThreads.startThreadCallersStayInside.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** A caller of startThread is inside when it calls, and does nothing during the call that would take it out:
    it neither closes the herd nor leaves its set, and no other thread removes it. *)
Lemma startThreadCallersStayInside_Proofs_complete : startThreadCallersStayInside_Obl_complete.
Proof.
  intros steps heldIn Hinside Hneither Honly h code c w [Hcalled | (m & Hm & Hbegun & Hpending)].
  { exact (Hinside h code c w Hcalled). }
  assert (forall k, m <= k -> k <= w -> inside heldIn steps c h k) as Hall; [| apply Hall; lia].
  apply (from_a_moment_on (fun k => k <= w -> inside heldIn steps c h k)).
  { intros _. apply (Hinside h code c m). apply begun_is_called. exact Hbegun. }
  intros k Hk IH Hkw. specialize (IH ltac:(lia)).
  assert (~ calledBy steps (Invocation_mk
      "ox.internal.ThreadHerd interruptAllAndJoinUntilCompleted :scala.Unit"%string [h]) c k /\
    ~ calledBy steps (Invocation_mk
      "java.util.concurrent.ConcurrentHashMap$.KeySetView remove java.lang.Object:scala.Boolean"%string
      [heldIn "ox.internal.ThreadHerd threads"%string h; c]) c k) as [Hnoclose Hnoleave].
  { destruct (Z.eq_dec k m) as [-> | Hne].
    - split; intros Hc;
        destruct (one_call_at_a_moment steps _ _ _ _ m Hc (begun_is_called _ _ _ _ Hbegun)) as [E _];
        discriminate E.
    - apply (Hneither h code c k). exists m. split; [lia | split; [exact Hbegun |]].
      intros Hover. apply Hpending. apply (over_later steps c m k w); [lia | exact Hover]. }
  destruct IH as [[Hown Hnot] | [Hfork Hstays]].
  - left. split; [exact Hown |]. intros (m1 & Hm1 & Hc1).
    assert (m1 < k \/ m1 = k) as [Hlt | ->] by lia.
    + apply Hnot. exists m1. split; [exact Hlt | exact Hc1].
    + apply Hnoclose. rewrite Hown. exact Hc1.
  - right. split.
    + destruct Hfork as (a & Ha & Hadd). exists a. split; [lia | exact Hadd].
    + intros (m1 & Hm1 & who & Hrem). assert (m1 < k \/ m1 = k) as [Hlt | ->] by lia.
      * apply Hstays. exists m1. split; [exact Hlt | exists who; exact Hrem].
      * pose proof (Honly h c who k Hrem) as ->. exact (Hnoleave Hrem).
Qed.
