Require Export FrFlowGen.OxThreads.aScopeEndsAfterItsHerdIsClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `scopedWithCapability`'s tree. It reads the thread's scope, sets it to the scope it was given, and
    applies a function of its own; that function applies the code to the scope, and then, whatever the code
    gave, asks the scope for its herd and closes it. Whatever follows (the scope's finalizers, the thread's scope
    set back), closing has completed by then. *)
Lemma aScopeEndsAfterItsHerdIsClosed_Proofs_complete : aScopeEndsAfterItsHerdIsClosed_Obl_complete.
Proof.
  intros heldIn history [N C] Hherd Hscope s code c from ended to Hdone.
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (module_not_atomic C "ox.unsupervised$package$" "scopedWithCapability"
      "1,ox.Ox,scala.Function1:java.lang.Object" Hat ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)). }
  assert (forall k, direct c from (history k) ->
    forall ended sp, history k = Event_Respond c from ended sp ->
    exists a closed b, (from < a /\ b <= k) /\ completedBy history (Invocation_mk
      L.ThreadHerd_interruptAllAndJoinUntilCompleted [heldIn L.OxError_herd s])
      c a closed b) as Hall.
  { refine (module_meets _ C "ox.unsupervised$package$" "scopedWithCapability"
      "1,ox.Ox,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl eq_refl
      ltac:(vm_compute; reflexivity) _).
    intros args k Hargs Hpassed.
    inversion Hargs as [| ? vscope ? rest Hvscope Hrest]; subst.
    apply vals_one in Hrest as (vcode & -> & Hvcode).
    inversion Hpassed as [| p1 v1 ps1 vs1 Hscopetyped Hpassed1]; subst.
    inversion Hpassed1 as [| p2 v2 ps2 vs2 Hcodetyped _]; subst. typed Hscopetyped. typed Hcodetyped.
    (* the thread's scope is read: that returns *)
    step. intros wget ysget Hwget _ Hysget Hmkget. apply args_none in Hysget as ->. split; [miss |].
    intros wgetd rget xget Hwgetd Hdoneget Hgivesget Hretget.
    destruct (proj1 (Hscope s) _ _ _ (done_by_someone Hdoneget)) as (yprevious & ->).
    destruct xget as [e | vprevious]; [contradiction |].
    (* and set to the scope: that returns *)
    step. intros wset ysset Hwset _ Hysset Hmkset. cbn in Hysset. apply args_one in Hysset as (yset & -> & Hyset).
    pose proof (one_name N _ _ _ Hyset Hvscope) as ->. split; [miss |].
    intros wsetd rset xset Hwsetd Hdoneset Hgivesset Hretset.
    rewrite (proj2 (Hscope s) _ _ _ (done_by_someone Hdoneset)) in Hgivesset.
    destruct xset as [e | u]; [contradiction |].
    (* its own function is applied *)
    step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    cbn in Hysg. apply args_none in Hysg as ->. split; [miss |].
    intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp.
    (* that function completes only after the herd is closed *)
    assert (exists a closed b, (wapp < a /\ b <= wappd) /\ completedBy history (Invocation_mk
      L.ThreadHerd_interruptAllAndJoinUntilCompleted [heldIn L.OxError_herd s]) c a closed b)
      as (a & closed & b & [Ha Hb] & Hclosed).
    { lazymatch type of Hyg with names _ _ (VCode ?fn) =>
        assert (written Code_files Code_classes fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
      assert (direct c wapp (history wappd)) as Hdirapp by (rewrite Hrespapp; cbn; auto).
      refine (function_meets (fun w => forall r sp, history w = Event_Respond c wapp r sp ->
        exists a closed b, (wapp < a /\ b <= w) /\ completedBy history (Invocation_mk
      L.ThreadHerd_interruptAllAndJoinUntilCompleted [heldIn L.OxError_herd s]) c a closed b)
        C Hinv eq_refl Hyg Hwritten _ wappd Hdirapp rapp spapp Hrespapp).
      intros args' k' Hargs' _. apply vals_none in Hargs' as ->.
      (* the code is applied to the scope: whatever it gives *)
      (* the code is applied to the scope: whatever it gives *)
      step. intros wcode mcode ycode yscode Hwcode _ Hmcode Hycode Hyscode Hinvcode. split; [miss |].
      intros wcoded rcode spcode xcode Hwcoded Hrespcode Hgivescode.
      (* whatever it gave, the scope is asked for its herd, and gives the herd it holds *)
      meets_head.
      all: step_rule; intros wherd ysherd Hwherd _ Hysherd Hmkherd; cbn in Hysherd;
        apply args_one in Hysherd as (yherdscope & -> & Hyherdscope);
        pose proof (one_name N _ _ _ Hyherdscope Hvscope) as ->; (split; [miss |]);
        intros wherdd rherd xherd Hwherdd Hdoneherd Hgivesherd Hretherd;
        rewrite (Hherd s _ _ _ (done_by_someone Hdoneherd)) in Hgivesherd;
        (destruct xherd as [e' | vherd]; [contradiction |]).
      (* and the herd is closed: whatever follows, that has completed *)
      all: meets_head.
      all: step_rule; intros wclose ysclose Hwclose _ Hysclose Hinvclose;
        (lazymatch type of Hysclose with Forall2 _ _ (receiver ?v ++ _) =>
           match goal with Hrecv : receiver v = _ |- _ => rewrite Hrecv in Hysclose end end);
        cbn [app] in Hysclose; apply args_one in Hysclose as (yclose & -> & Hyclose);
        pose proof (one_name N _ _ _ Hyclose Hgivesherd) as ->; (split; [miss |]);
        intros wclosed rclose spclose xclose Hwclosed Hrespclose Hgivesclose.
      all: apply meets_from; intros k0 Hk0 r0 sp0 Hr0; exists wclose, rclose, (wclosed + 1);
        (split; [split; lia | right; split; [exists (Some wapp); exact Hinvclose |
          exists spclose; replace (wclosed + 1 - 1) with wclosed by lia; exact Hrespclose]]). }
    (* then the thread's scope is set back: whatever all that gives, the herd was closed before *)
    apply meets_from. intros k0 Hk0 r0 sp0 Hr0. exists a, closed, b. split; [split; lia | exact Hclosed]. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) ended sp Hend) as (a & closed & b & [Ha Hb] & Hclosed).
  exists a, closed, b. split; [split; [exact Ha | lia] | exact Hclosed].
Qed.
