Require Export FrFlowGen.OxThreads.forkUserStartsAThread.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `forkUser`'s tree. It asks the scope for itself without an error mode, which gives a scope that holds
    the same herd, and calls `forkUserError` in that scope; what that gives, it gives. So a call that returns comes
    after `forkUserError` returned, and so after a call of `startThread` on the herd returned. *)
Lemma forkUserStartsAThread_Proofs_complete : forkUserStartsAThread_Obl_complete.
Proof.
  intros heldIn history [N C] Hforkerror Hasno code s c from fork to [Hsmade Hdone].
  pose proof Hsmade as (wm & m0 & b0 & ins0 & hs0 & _ & Hmk). destruct (made_named C Hmk) as [r Hs].
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (module_not_atomic C "ox.fork$package$" "forkUser" "1,scala.Function0,ox.Ox:ox.Fork" Hat
      ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)). }
  assert (forall k, direct c from (history k) ->
    forall ended sp, history k = Event_Respond c from ended sp -> forall fork, ended = Response_Returned fork ->
    exists run a b, (from < a /\ b <= k + 1) /\
      completedBy history (Invocation_mk "ox.internal.ThreadHerd startThread scala.Function0:scala.Unit"
        [heldIn "ox.OxError herd" s; run]) c a (Response_Returned Value_Unit_) b) as Hall.
  { refine (module_meets _ C "ox.fork$package$" "forkUser" "1,scala.Function0,ox.Ox:ox.Fork" Hcall
      ltac:(vm_compute; reflexivity) eq_refl eq_refl ltac:(vm_compute; reflexivity) _).
    intros args k Hargs Hpassed.
    inversion Hargs as [| ? vcode ? rest Hvcode Hrest]; subst.
    apply vals_one in Hrest as (vscope & -> & Hvscope).
    inversion Hpassed as [| p1 v1 ps1 vs1 Hcodetyped Hpassed1]; subst.
    inversion Hpassed1 as [| p2 v2 ps2 vs2 Hscopetyped _]; subst. typed Hcodetyped. typed Hscopetyped.
    pose proof (names_one N _ _ _ Hvscope Hs) as ->.
    (* the scope is asked for itself without an error mode: that gives a scope with the same herd *)
    step. intros wno ysno Hwno _ Hysno Hinvno.
    cbn in Hysno. apply args_one in Hysno as (yno & -> & Hyno).
    pose proof (one_name N _ _ _ Hyno Hs) as ->. split; [miss |].
    intros wnod rno spno xno Hwnod Hrespno Hgivesno.
    destruct xno as [e | vother].
    { meets_head. apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp fork' ->. rewrite Hrr in Hresp.
      injection Hresp as -> _. destruct Hgives. }
    destruct rno as [yother | yother]; [| contradiction].
    destruct (Hasno s wno yother (wnod + 1)) as [Hothermade Hsameherd].
    { split; [exact Hsmade |]. exists c. right. split; [exists (Some from); exact Hinvno |]. exists spno.
      replace (wnod + 1 - 1) with wnod by lia. exact Hrespno. }
    (* forkError is called in that scope: what it gives is what the call gives *)
    step. intros wfe ysfe Hwfe _ Hysfe Hinvfe. cbn in Hysfe.
    apply args_two in Hysfe as (yo & ycode & -> & Hyo & Hycode).
    pose proof (one_name N _ _ _ Hyo Hgivesno) as ->. split; [miss |].
    intros wfed rfe spfe xfe Hwfed Hrespfe Hgivesfe.
    meets_head.
    all: apply meets_ret; intros rr Hk _ Hrr Hgives ended' sp' Hresp fork' ->; rewrite Hrr in Hresp;
      injection Hresp as -> _.
    all: try (destruct Hgives; fail).
    destruct rfe as [yfork | yfork]; [| contradiction].
    destruct (Hforkerror ycode yother c wfe yfork (wfed + 1)) as (run & a & b & [[[Ha Hb] _] Hst]).
    { split; [exact Hothermade |]. right. split; [exists (Some from); exact Hinvfe |]. exists spfe.
      replace (wfed + 1 - 1) with wfed by lia. exact Hrespfe. }
    rewrite Hsameherd in Hst. exists run, a, b. split; [split; lia | exact Hst]. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) _ sp Hend fork eq_refl) as (run & a & b & [Ha Hb] & Hst).
  exists run, a, b. split; [split; [exact Ha | lia] | exact Hst].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma forkUserStartsAThread_Proofs_feasible : forkUserStartsAThread_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros code s c from fork to [_ H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros s from other to [_ [who H]]. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
