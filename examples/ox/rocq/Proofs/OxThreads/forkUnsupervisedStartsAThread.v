Require Export FrFlowGen.OxThreads.forkUnsupervisedStartsAThread.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `forkUnsupervised`'s tree. It makes a future, asks the scope for its herd, which gives the herd the
    scope holds, and calls `startThread` on that herd. If one of the three throws, so does the call. So a call
    that returns comes after `startThread` returned. *)
Lemma forkUnsupervisedStartsAThread_Proofs_complete : forkUnsupervisedStartsAThread_Obl_complete.
Proof.
  intros heldIn history [N C] Hherd code s c from fork to Hdone.
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (module_not_atomic C "ox.fork$package$" "forkUnsupervised"
      "1,scala.Function0,ox.OxUnsupervised:ox.UnsupervisedFork" Hat ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)). }
  assert (forall k, direct c from (history k) ->
    forall ended sp, history k = Event_Respond c from ended sp -> forall fork, ended = Response_Returned fork ->
    exists run a b, ((from < a /\ b <= k + 1) /\ itselfMakes history (Invocation_mk
      L.ThreadHerd_startThread [heldIn L.OxError_herd s; run]) c from a) /\
      completedBy history (Invocation_mk L.ThreadHerd_startThread
        [heldIn L.OxError_herd s; run]) c a (Response_Returned Value_Unit_) b) as Hall.
  { refine (module_meets _ C "ox.fork$package$" "forkUnsupervised"
      "1,scala.Function0,ox.OxUnsupervised:ox.UnsupervisedFork" Hcall ltac:(vm_compute; reflexivity) eq_refl eq_refl
      ltac:(vm_compute; reflexivity) _).
    intros args k Hargs Hpassed.
    inversion Hargs as [| ? vcode ? rest Hvcode Hrest]; subst.
    apply vals_one in Hrest as (vscope & -> & Hvscope).
    inversion Hpassed as [| p1 v1 ps1 vs1 Hcodetyped Hpassed1]; subst.
    inversion Hpassed1 as [| p2 v2 ps2 vs2 Hscopetyped _]; subst. typed Hcodetyped. typed Hscopetyped.
    (* a future is made *)
    step. intros wnew ysnew Hwnew _ Hysnew Hmknew. split; [miss |].
    intros wnewd rnew xnew Hwnewd Hdonenew Hgivesnew Hretnew.
    meets_head.
    { apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp fork' ->. rewrite Hrr in Hresp.
      injection Hresp as -> _. destruct Hgives. }
    (* the scope is asked for its herd, and gives the herd it holds *)
    step_rule. intros wherd ysherd Hwherd _ Hysherd Hmkherd. cbn in Hysherd.
    apply args_one in Hysherd as (yherdscope & -> & Hyherdscope).
    pose proof (one_name N _ _ _ Hyherdscope Hvscope) as ->. split; [miss |].
    intros wherdd rherd xherd Hwherdd Hdoneherd Hgivesherd Hretherd.
    rewrite (Hherd s _ _ _ (done_by_someone Hdoneherd)) in Hgivesherd.
    destruct xherd as [e' | vherd]; [contradiction |].
    (* and startThread is called on it: whatever follows, that has returned *)
    step_typed. intros wst ysst Hwst _ Hysst Hinvst.
    (lazymatch type of Hysst with Forall2 _ _ (receiver ?v ++ _) =>
       match goal with Hrecv : receiver v = _ |- _ => rewrite Hrecv in Hysst end end).
    cbn [app] in Hysst. apply args_two in Hysst as (yh & yrun & -> & Hyh & Hyrun).
    pose proof (one_name N _ _ _ Hyh Hgivesherd) as ->. split; [miss |].
    intros wstd rst spst xst Hwstd Hrespst Hgivesst Hretst.
    destruct xst as [e | vst].
    { meets_head. apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp fork' ->. rewrite Hrr in Hresp.
      injection Hresp as -> _. destruct Hgives. }
    typed Hretst. pose proof (returned_unit N rst Hgivesst) as ->.
    apply meets_from. intros k0 Hk0 ended0 sp0 Hr0 fork0 _. exists yrun, wst, (wstd + 1).
    split; [split; [split; lia | left; exact Hinvst] |].
    right. split; [exists (Some from); exact Hinvst |].
    exists spst. replace (wstd + 1 - 1) with wstd by lia. exact Hrespst. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) _ sp Hend fork eq_refl)
    as (run & a & b & [[Ha Hb] Hmakes] & Hst).
  exists run, a, b. split; [split; [split; [exact Ha | lia] | exact Hmakes] | exact Hst].
Qed.

(** Its part can hold: an execution in which nothing happens meets it. *)
