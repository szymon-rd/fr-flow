Require Export FrFlowGen.OxThreads.closingsFunctionsInterrupt.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree, three deep. Each of the two functions
    closing passes to a traversal first applies, to the thread it is given, the function that interrupts a thread
    once, and goes on only once that has completed: by then the thread has been interrupted. *)
Lemma closingsFunctionsInterrupt_Proofs_complete : closingsFunctionsInterrupt_Obl_complete.
Proof.
  intros heldIn history [N C] Happly Hjoin Hmade h f x c k r b
    [(from & a0 & [[Ha0 Hcalled] Hmakes]) Hdone].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r0 & inside & Hh & Hcall).
  revert x c k r b Ha0 Hdone.
  pose proof (makes_direct Hmakes) as Hdirect. revert f Hmakes. revert a0 Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k0 Hargs _. apply vals_none in Hargs as ->.
  (* the owner is checked and the flag set; closing's variables are made; then it loops *)
  pass_to_loop.
  meets_head. apply meets_iter with (J := fun _ _ _ => True); [| exact I].
  intros tr1 wt s1 HJ IH.
  pass. pass. meets_head; [pass | repeat pass |].
  (* the first traversal *)
  pass.
  step. intros wt1 yst1 Hwt1 _ Hyst1 Hmk1. apply args_two in Hyst1 as (yset1 & yfun1 & -> & _ & Hyfun1).
  split.
  { intros fe Hit xe ce ke re be Hlt Hdone.
    pose proof (makes_one Hmk1 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun1 with names _ _ (VCode ?fn) =>
      assert (written Code_files Code_classes fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Hdone as [[(ins1 & sp1 & Hat1) _] | [[inside1 Hcall1] [sp1 Hend1]]];
      [exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun1 Hwritten) |].
    assert (direct ce ke (history (be - 1))) as Hdir1 by (rewrite Hend1; cbn; auto).
    remember (be - 1) as last eqn:Elast. assert (be = last + 1) as -> by lia. clear Elast.
    revert re sp1 Hend1. revert Hdir1. revert last.
    refine (function_meets _ C Hcall1 eq_refl Hyfun1 Hwritten _).
    intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & Hxe).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    (* it applies the function that interrupts a thread once to the thread it is given *)
    step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & Hythread). pose proof (one_name N _ _ _ Hythread Hxe) as ->.
    split; [miss |]. intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp.
    destruct (Happly h fe xe ce ke yg xe wapp rapp (wappd + 1)) as (ifrom & value & ito & Hito & who & Hint).
    { split; [split; [split |] |].
      - exists from, wt1. split; [split; [exact Hlt | exact Hcalled] | exact Hit].
      - left. exists inside1. exact Hcall1.
      - left. exact Hinv.
      - right. split; [exists (Some ke); exact Hinv |]. exists spapp.
        replace (wappd + 1 - 1) with wappd by lia. exact Hrespapp. }
    (* whatever it does next, it ends after that *)
    meets_head.
    all: repeat (lazymatch goal with
      | |- meets _ _ _ _ _ _ _ _ _ (Running (Ret _)) _ => fail
      | |- _ => idtac
      end; step_rule; intros; (split; [miss |]); intros; meets_head).
    all: apply meets_ret; intros rr Hle _ Hrr Hgives re sp1 Hre.
    all: exists ifrom, value, ito; (split; [lia | exists who; exact Hint]). }
  intros wu1 rt1 xt1 Hwu1 _ _ _. meets_head; [pass |].
  (* the second *)
  pass.
  step. intros wt2 yst2 Hwt2 _ Hyst2 Hmk2. apply args_two in Hyst2 as (yset2 & yfun2 & -> & _ & Hyfun2).
  split.
  { intros fe Hit xe ce ke re be Hlt Hdone.
    pose proof (makes_one Hmk2 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun2 with names _ _ (VCode ?fn) =>
      assert (written Code_files Code_classes fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Hdone as [[(ins1 & sp1 & Hat1) _] | [[inside1 Hcall1] [sp1 Hend1]]];
      [exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun2 Hwritten) |].
    assert (direct ce ke (history (be - 1))) as Hdir1 by (rewrite Hend1; cbn; auto).
    remember (be - 1) as last eqn:Elast. assert (be = last + 1) as -> by lia. clear Elast.
    revert re sp1 Hend1. revert Hdir1. revert last.
    refine (function_meets _ C Hcall1 eq_refl Hyfun2 Hwritten _).
    intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & Hxe).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    (* it applies the function that interrupts a thread once to the thread it is given *)
    step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & Hythread). pose proof (one_name N _ _ _ Hythread Hxe) as ->.
    split; [miss |]. intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp.
    destruct (Happly h fe xe ce ke yg xe wapp rapp (wappd + 1)) as (ifrom & value & ito & Hito & who & Hint).
    { split; [split; [split |] |].
      - exists from, wt2. split; [split; [exact Hlt | exact Hcalled] | exact Hit].
      - left. exists inside1. exact Hcall1.
      - left. exact Hinv.
      - right. split; [exists (Some ke); exact Hinv |]. exists spapp.
        replace (wappd + 1 - 1) with wappd by lia. exact Hrespapp. }
    (* whatever it does next, it ends after that *)
    meets_head.
    (* where that returned, the thread is joined: the join returns, or throws an interruption *)
    all: try (step_rule; intros wj ysj Hwj _ Hysj Hmkj; apply args_one in Hysj as (ytj & -> & _);
      (split; [miss |]); intros wjd rj xj Hwjd Hdonej Hgivesj _;
      destruct (Hjoin _ _ _ _ (done_by_someone Hdonej)) as [-> | ->];
      [ destruct xj as [e | u']; [contradiction |]
      | destruct xj as [e | u']; [| contradiction]; apply threw_interruption in Hgivesj as -> ];
      meets_head).
    all: repeat (lazymatch goal with
      | |- meets _ _ _ _ _ _ _ _ _ (Running (Ret _)) _ => fail
      | |- _ => idtac
      end; step_rule; intros; (split; [miss |]); intros; meets_head).
    all: apply meets_ret; intros rr Hle _ Hrr Hgives re sp1 Hre.
    all: exists ifrom, value, ito; (split; [lia | exists who; exact Hint]). }
  intros wu2 rt2 xt2 Hwu2 _ _ _. meets_head; [pass |].
  (* then the next turn *)
  apply IH; first [lia | exact I].
Qed.
