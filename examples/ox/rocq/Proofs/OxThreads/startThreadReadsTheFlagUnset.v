Require Export FrFlowGen.OxThreads.startThreadReadsTheFlagUnset.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.assertNotShuttingDown`'s tree: it reads the herd's flag and throws if it is set, so a
    call of it that returns has read the flag unset. *)
Lemma assertNotShuttingDown_returns {heldIn} {history : Z -> Event} {N h r c inside w1} :
  conforms Code_files Code_table Code_classes N history -> aHerdKeepsItsFields_claim heldIn history ->
  names N h (vref "ox.internal.ThreadHerd" r) ->
  history w1 = Event_Invoke c inside (Invocation_mk L.ThreadHerd_assertNotShuttingDown [h]) ->
  forall w, direct c w1 (history w) -> forall v sp, history w = Event_Respond c w1 (Response_Returned v) sp ->
    exists a b, (w1 <= a /\ b <= w) /\ exists who, completedBy history
      (Invocation_mk L.AtomicBoolean_get
        [heldIn L.ThreadHerd_shutdownInProgress h]) who a (Response_Returned (Value_Bool_ False)) b.
Proof.
  intros C Hfields Hh Hcall.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "assertNotShuttingDown" ":scala.Unit") Hcall Hh
    eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* the flag is read *)
  step. intros wr vf y Hwr _ Hy Hty Hread. split; [miss |]. apply (proj2 (proj1 (Hfields h))) in Hread. subst y.
  (* and asked what it holds *)
  step. intros wg ys Hwg _ Hys Hmk. split; [miss |]. intros wd a x Hwd Hget Hgives Htyped.
  apply args_one in Hys as (y0 & -> & Hy0). rewrite (one_name N _ _ _ Hy0 Hy) in Hget.
  (* it threw, or it is set: the call throws; it is unset: the call returns, and this read is the one *)
  step; [miss | miss |]. intros r' Hk _ _ _ v' sp _.
  destruct a as [answer | thrown]; [| contradiction]. apply named_bool in Hgives. subst answer.
  exists wg, wd. split; [lia |]. exists c. exact (done_completed Hget).
Qed.

(** Proven of `ThreadHerd.startThread`'s tree: its first step is a call of `assertNotShuttingDown`; what
    `startThread` does after is done only once that call has returned. *)
Lemma startThreadReadsTheFlagUnset_Proofs_complete : startThreadReadsTheFlagUnset_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hfields h code c t from w [Hcalled Hthen].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  assert (forall k, direct c from (history k) ->
    (exists s t, itselfMakes history (Invocation_mk
        L.KeySetView_add [s; t]) c from k) \/
    (exists sp, history k = Event_Respond c from (Response_Returned Value_Unit_) sp) ->
    exists a b, (from <= a /\ b <= k) /\ exists who, completedBy history
      (Invocation_mk L.AtomicBoolean_get
        [heldIn L.ThreadHerd_shutdownInProgress h]) who a (Response_Returned (Value_Bool_ False)) b)
    as Hall.
  { refine (method_meets _ C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh
      eq_refl _).
    intros args k Hargs _. apply vals_one in Hargs as (vcode & -> & _).
    (* assertNotShuttingDown is called *)
    step. intros w1 ys Hw1 _ Hys Hinv. split; [miss |]. intros w2 rr sp x Hw2 Hresp Hgives.
    apply args_one in Hys as (y0 & -> & Hy0). pose proof (one_name N _ _ _ Hy0 Hh) as ->.
    (* it threw: so does startThread; it returned: the flag has been read unset, before all that follows *)
    destruct x as [e | v]; [pass |]. destruct rr as [yv | thrown]; [| contradiction].
    destruct (assertNotShuttingDown_returns C Hfields Hh Hinv w2 ltac:(rewrite Hresp; cbn; auto) yv sp Hresp)
      as (a & b & [Ha Hb] & Hseen).
    apply meets_from. intros k' Hk' _. exists a, b. split; [lia | exact Hseen]. }
  destruct Hthen as [Hadd | [[(ins & sp & Hat) _] | [_ [sp Hend]]]].
  - apply (Hall w (makes_direct Hadd)). left. eexists. eexists. exact Hadd.
  - rewrite Hcall in Hat. discriminate Hat.
  - destruct (Hall (w - 1) ltac:(rewrite Hend; cbn; auto) (or_intror (ex_intro _ sp Hend)))
      as (a & b & [Ha Hb] & Hd).
    exists a, b. split; [lia | exact Hd].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
