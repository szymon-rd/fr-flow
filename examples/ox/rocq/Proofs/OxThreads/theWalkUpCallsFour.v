Require Export FrFlowGen.OxThreads.theWalkUpCallsFour.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.verifyCurrentThreadInScopeTree`'s tree, twice over. The function the check applies is
    the one written there, `doAssert`; a call of it, whoever makes it, asks the scope for its herd, the herd
    whether the thread is its owner or one of its threads, the scope for its parent, and applies itself to the
    parent. *)
Lemma theWalkUpCallsFour_Proofs_complete : theWalkUpCallsFour_Obl_complete.
Proof.
  intros history [N C] Hmade g scope (h & who & scope0 & from & a & Hcalled & Hmakes) k2 inner w
    (c2 & (inside2 & Hcall2) & Hmakes2).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "verifyCurrentThreadInScopeTree" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes2) as Hdirect2. revert inner Hmakes2. revert w Hdirect2.
  revert scope c2 k2 inside2 Hcall2.
  pose proof (makes_direct Hmakes) as Hdirect. revert g scope0 Hmakes. revert a Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "verifyCurrentThreadInScopeTree" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* the current thread and its scope are asked for; with a scope, the check applies its function to it *)
  pass. pass. meets_head; [pass | repeat pass |].
  step_rule. intros wapp m yf ysapp _ _ Hm Hyf Hysapp Hinv. cbv [called_as] in Hm. subst m.
  apply args_one in Hysapp as (yscope & -> & _).
  split; [| intros; pass].
  intros g scope0 Hit scope c2 k2 inside2 Hcall2.
  pose proof (makes_one (or_introl Hinv) Hit) as Esame. injection Esame as -> ->.
  lazymatch type of Hyf with names _ _ (VCode ?fn) =>
    assert (written Code_files Code_classes fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  (* a call of that function *)
  refine (function_meets _ C Hcall2 eq_refl Hyf Hwritten _).
  intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vscope & -> & _).
  cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hscope _]; subst. typed Hscope.
  (* the scope's herd *)
  step. intros wh ysh Hwh _ Hysh Hmkh. apply args_one in Hysh as (yscope1 & -> & _).
  split; [intros inner Hitmk; rewrite <- (makes_one Hmkh Hitmk); left; left; left; eauto |].
  intros whd rh xh Hwhd Hdoneh Hgivesh Hreth.
  meets_head; [pass |].
  (* is asked whether the thread is its owner or one of its threads: its answer is a truth value *)
  step_rule. intros wm ysm Hwm _ Hysm Hinvm.
  lazymatch type of Hysm with Forall2 _ _ (receiver ?v ++ _) =>
    match goal with Hrecv : receiver v = _ |- _ => rewrite Hrecv in Hysm end end.
  cbn [app] in Hysm. apply args_two in Hysm as (yherd & ythread & -> & _ & _).
  split; [intros inner Hitmk; rewrite <- (makes_one (or_introl Hinvm) Hitmk); left; right; eauto |].
  intros wmd rm spm xm Hwmd Hrespm Hgivesm.
  destruct xm as [e | vm]; [pass |].
  assert (calledBy history (Invocation_mk
    L.ThreadHerd_isOwnerOrHerdThread [yherd; ythread]) c2 wm)
    as Hcalledm by (left; exists (Some k2); exact Hinvm).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "isOwnerOrHerdThread" "java.lang.Thread:scala.Boolean") C
    (Hmade yherd wm ltac:(unfold calledOn; eauto 14)) eq_refl Hcalledm) as (rherd & insidem & Hyherd & Hcallm).
  destruct (isOwnerOrHerdThread_returns C Hyherd Hcallm wmd ltac:(rewrite Hrespm; cbn; auto) _ _ _
    Hrespm Hgivesm) as (bm & ->).
  (* yes: the function returns; no: the scope's parent is asked for *)
  meets_head; [repeat pass |].
  step_rule. intros wp ysp Hwp _ Hysp Hmkp. apply args_one in Hysp as (yscope2 & -> & _).
  split; [intros inner Hitmk; rewrite <- (makes_one Hmkp Hitmk); left; left; right; eauto |].
  intros wpd rp xp Hwpd Hdonep Hgivesp Hretp.
  (* it threw; it is none, and the function throws; it is some scope; it is no object, and the match fails *)
  meets_head; [pass | pass | | pass].
  (* the function applies itself to that scope *)
  step_rule. intros wrec m yrec ysrec Hwrec _ Hm Hyrec Hysrec Hinvrec. cbv [called_as] in Hm. subst m.
  apply args_one in Hysrec as (yparent & -> & _).
  pose proof (one_name N _ _ _ Hyrec Hyf) as ->.
  split; [intros inner Hitmk; rewrite <- (makes_one (or_introl Hinvrec) Hitmk); right; eauto |].
  intros; repeat pass.
Qed.
