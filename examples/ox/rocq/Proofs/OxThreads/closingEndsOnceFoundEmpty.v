Require Export FrFlowGen.OxThreads.closingEndsOnceFoundEmpty.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree: past its check and the flag it sets, it
    loops, each turn asking the herd's set whether it is empty; it leaves the loop, and so completes, only on a
    yes. *)
Lemma closingEndsOnceFoundEmpty_Proofs_complete : closingEndsOnceFoundEmpty_Obl_complete.
Proof.
  intros heldIn history [N C] Hempty Htraversals Hset Hmade Hfields Hcurrent h from response to Hdone.
  pose proof (completed_was_called _ _ _ _ _ _ Hdone) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled)
    as (r & inside & Hh & Hcall).
  destruct Hdone as [[(ins & spawns & Hat) _] | [_ [spawns Hend]]]; [rewrite Hcall in Hat; discriminate Hat |].
  assert (forall k, direct (heldIn L.ThreadHerd_herdOwner h) from (history k) ->
    forall resp sp, history k = Event_Respond (heldIn L.ThreadHerd_herdOwner h) from resp sp ->
    exists a b, (from < a /\ b <= k) /\ completedBy history
      (Invocation_mk L.CollectionView_isEmpty
        [heldIn L.ThreadHerd_threads h]) (heldIn L.ThreadHerd_herdOwner h) a
      (Response_Returned (Value_Bool_ True)) b) as Hall.
  { refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
      Hcall Hh eq_refl _).
    intros args k Hargs _. apply vals_none in Hargs as ->.
    (* assertOnOwnerThread is called: it returns, the caller being the herd's owner *)
    step. intros w1 ys Hw1 _ Hys Hinv. split; [miss |]. intros w2 rr sp x Hw2 Hresp Hgives.
    apply args_one in Hys as (y0 & -> & Hy0). pose proof (one_name N _ _ _ Hy0 Hh) as ->.
    destruct x as [e | v].
    { exfalso. destruct rr as [y | y]; [contradiction |].
      exact (assertOnOwnerThread_returns C (proj2 (proj1 (proj1 (Hfields h)))) Hcurrent Hh Hinv w2
        ltac:(rewrite Hresp; cbn; auto) y sp Hresp). }
    (* the flag is read, and set: setting does not throw *)
    pass.
    step. intros ws yss Hws _ Hyss Hmk. split; [miss |]. intros wd a x Hwd Hsetd Hgives' _.
    apply args_two in Hyss as (y1 & y2 & -> & _ & Hy2). apply named_bool in Hy2. subst y2.
    rewrite (Hset _ _ _ _ _ (done_by_someone Hsetd)) in Hgives'.
    destruct x as [e | u]; [contradiction |].
    (* its two variables are made; then it loops: every turn comes after the call *)
    repeat pass. meets_head. apply meets_iter with (J := fun _ w _ => from < w); [| lia].
    intros tr1 wt s1 HJ IH.
    (* a turn: the set is read, and asked whether it is empty; asking does not throw *)
    step. intros wr vset yset Hwr _ Hyset Htyset Hread. split; [miss |].
    apply (proj2 (Hfields h)) in Hread. subst yset.
    step. intros we yse Hwe _ Hyse Hmke. split; [miss |]. intros wf ae xe Hwf Hask Hgivese Htye.
    apply args_one in Hyse as (y3 & -> & Hy3). pose proof (one_name N _ _ _ Hy3 Hyset) as ->.
    destruct (Hempty _ _ _ _ (done_by_someone Hask)) as [-> | ->]; (destruct xe as [e | answer]; [contradiction |]);
      typed Htye; apply bool_named in Hgivese.
    { (* yes: whatever the call does after, it has been answered yes *)
      apply meets_from. intros k' Hk' resp sp' _. exists we, wf. split; [lia | exact (done_completed Hask)]. }
    (* no: the set is traversed twice, and neither traversal throws; then the next turn *)
    destruct b; [destruct (proj2 Hgivese eq_refl) |].
    step. intros wr1 vset1 yset1 Hwr1 _ Hyset1 Htyset1 Hread1. split; [miss |].
    apply (proj2 (Hfields h)) in Hread1. subst yset1.
    step. intros wt1 yst1 Hwt1 _ Hyst1 Hmkt1. split; [miss |]. intros wu1 at1 xt1 Hwu1 Htrav1 Hgt1 _.
    apply args_two in Hyst1 as (ya1 & yf1 & -> & Hya1 & _). pose proof (one_name N _ _ _ Hya1 Hyset1) as ->.
    rewrite (Htraversals h yf1 from wt1 wu1 at1 (conj (conj Hcalled (done_made Htrav1)) (done_completed Htrav1)))
      in Hgt1. destruct xt1 as [e | u1]; [contradiction |].
    step. intros wr2 vset2 yset2 Hwr2 _ Hyset2 Htyset2 Hread2. split; [miss |].
    apply (proj2 (Hfields h)) in Hread2. subst yset2.
    step. intros wt2 yst2 Hwt2 _ Hyst2 Hmkt2. split; [miss |]. intros wu2 at2 xt2 Hwu2 Htrav2 Hgt2 _.
    apply args_two in Hyst2 as (ya2 & yf2 & -> & Hya2 & _). pose proof (one_name N _ _ _ Hya2 Hyset2) as ->.
    rewrite (Htraversals h yf2 from wt2 wu2 at2 (conj (conj Hcalled (done_made Htrav2)) (done_completed Htrav2)))
      in Hgt2. destruct xt2 as [e | u2]; [contradiction |].
    meets_head. apply IH; lia. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) response spawns Hend) as (a & b & [Ha Hb] & Hd).
  exists a, b. split; [lia | exact Hd].
Qed.
