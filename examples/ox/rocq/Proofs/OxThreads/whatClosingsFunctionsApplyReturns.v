Require Export FrFlowGen.OxThreads.whatClosingsFunctionsApplyReturns.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree, three deep: each traversal is given a
    function written there; run, it applies `interruptIfNeeded`; run, that reads the threads interrupted so
    far, interrupts the thread if it is not among them, writes it among them, and returns. *)
Lemma whatClosingsFunctionsApplyReturns_Proofs_complete : whatClosingsFunctionsApplyReturns_Obl_complete.
Proof.
  intros heldIn history [N C] Hjoin Hinterrupt Hmade h f x c k g t a r b
    [[[(from & a0 & [[_ Hcalled] Hmakes]) Haccept] Happlies] Hdone].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r0 & inside & Hh & Hcall).
  revert x c k g t a r b Haccept Happlies Hdone.
  pose proof (makes_direct Hmakes) as Hdirect. revert f Hmakes. revert a0 Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k0 Hargs _. apply vals_none in Hargs as ->.
  (* up to the loop, and in a turn up to the first traversal *)
  repeat pass. meets_head. apply meets_iter with (J := fun _ w _ => from < w); [| lia].
  intros tr1 wt s1 HJ IH.
  pass. pass. meets_head; [pass | repeat pass |].
  (* the first traversal: its function applies `interruptIfNeeded`, and no more *)
  pass.
  step. intros wt1 yst1 Hwt1 _ Hyst1 Hmk1. apply args_two in Hyst1 as (yset1 & yfun1 & -> & _ & Hyfun1).
  split.
  { intros fe Hit xe ce ke ge te ae re be Haccept Happlies Hdone.
    pose proof (makes_one Hmk1 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun1 with names _ _ (VCode ?fn) =>
      assert (written Code_files Code_classes fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Haccept as [[inside1 Hcall1] | (a1 & inside1 & sp1 & Hat1)];
      [| exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun1 Hwritten)].
    pose proof (makes_direct Happlies) as Hdirect1. revert ge te Happlies re be Hdone. revert ae Hdirect1.
    refine (function_meets _ C Hcall1 eq_refl Hyfun1 Hwritten _).
    intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & _).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    (* it applies `interruptIfNeeded` to the thread *)
    step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & _).
    split; [| intros; repeat pass].
    intros gg tg Hitg rg bg Hdoneg. pose proof (makes_one (or_introl Hinv) Hitg) as Eg. injection Eg as -> ->.
    lazymatch type of Hyg with names _ _ (VCode ?fn) =>
      assert (written Code_files Code_classes fn) as Hwritteng by (apply written_function; vm_compute; reflexivity) end.
    destruct Hdoneg as [[(insg & spg & Hatg) _] | [_ [spg Hendg]]]; [rewrite Hinv in Hatg; discriminate Hatg |].
    assert (direct ce wapp (history (bg - 1))) as Hdirg by (rewrite Hendg; cbn; auto).
    revert rg spg Hendg. revert Hdirg. generalize (bg - 1).
    refine (function_meets _ C Hinv eq_refl Hyg Hwritteng _).
    intros argsg kg Hargsg Hgiveng. apply vals_one in Hargsg as (vthreadg & -> & _).
    cbv beta iota delta [given] in Hgiveng. inversion Hgiveng as [| pi vi psi vsi Hthreadg _]; subst.
    typed Hthreadg.
    (* the threads interrupted so far are read: the thread is among them, and the function returns *)
    pass. meets_head.
    { apply meets_ret. intros rr _ _ Hrr Hgives rg spg Hrg. rewrite Hrr in Hrg. injection Hrg as <- _.
      exact (returned_unit N _ Hgives). }
    (* or it is not: it is interrupted, which returns *)
    step_rule. intros wint ysint Hwint _ Hysint Hmkint. apply args_one in Hysint as (ytint & -> & _).
    split; [miss |]. intros wintd rint xint Hwintd Hdoneint Hgivesint _.
    rewrite (Hinterrupt _ _ _ _ (done_by_someone Hdoneint)) in Hgivesint.
    destruct xint as [e | u]; [contradiction |].
    (* the threads interrupted are read again, and written with the thread among them; it returns *)
    pass. pass. pass. meets_head.
    apply meets_ret. intros rr _ _ Hrr Hgives rg spg Hrg. rewrite Hrr in Hrg. injection Hrg as <- _.
    exact (returned_unit N _ Hgives). }
  intros wu1 rt1 xt1 Hwu1 _ _ _. meets_head; [pass |].
  (* the second: its function applies it, then joins the thread *)
  pass.
  step. intros wt2 yst2 Hwt2 _ Hyst2 Hmk2. apply args_two in Hyst2 as (yset2 & yfun2 & -> & _ & Hyfun2).
  split.
  { intros fe Hit xe ce ke ge te ae re be Haccept Happlies Hdone.
    pose proof (makes_one Hmk2 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun2 with names _ _ (VCode ?fn) =>
      assert (written Code_files Code_classes fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Haccept as [[inside1 Hcall1] | (a1 & inside1 & sp1 & Hat1)];
      [| exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun2 Hwritten)].
    pose proof (makes_direct Happlies) as Hdirect1. revert ge te Happlies re be Hdone. revert ae Hdirect1.
    refine (function_meets _ C Hcall1 eq_refl Hyfun2 Hwritten _).
    intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & _).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    (* it applies `interruptIfNeeded` to the thread *)
    step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & _).
    split; [| intros wappd rapp spapp xapp Hwappd _ _; meets_head; [pass |];
      (* then it joins the thread: that returns, or throws an interruption, which the function catches *)
      step_rule; intros wj ysj Hwj _ Hysj Hmkj; apply args_one in Hysj as (ytj & -> & _); (split; [miss |]);
      intros wjd rj xj Hwjd Hdonej Hgivesj _;
      destruct (Hjoin _ _ _ _ (done_by_someone Hdonej)) as [-> | ->];
      [ destruct xj as [e | u]; [contradiction |]; repeat pass
      | destruct xj as [e | u]; [| contradiction]; apply threw_interruption in Hgivesj as ->; repeat pass ]].
    intros gg tg Hitg rg bg Hdoneg. pose proof (makes_one (or_introl Hinv) Hitg) as Eg. injection Eg as -> ->.
    lazymatch type of Hyg with names _ _ (VCode ?fn) =>
      assert (written Code_files Code_classes fn) as Hwritteng by (apply written_function; vm_compute; reflexivity) end.
    destruct Hdoneg as [[(insg & spg & Hatg) _] | [_ [spg Hendg]]]; [rewrite Hinv in Hatg; discriminate Hatg |].
    assert (direct ce wapp (history (bg - 1))) as Hdirg by (rewrite Hendg; cbn; auto).
    revert rg spg Hendg. revert Hdirg. generalize (bg - 1).
    refine (function_meets _ C Hinv eq_refl Hyg Hwritteng _).
    intros argsg kg Hargsg Hgiveng. apply vals_one in Hargsg as (vthreadg & -> & _).
    cbv beta iota delta [given] in Hgiveng. inversion Hgiveng as [| pi vi psi vsi Hthreadg _]; subst.
    typed Hthreadg.
    (* the threads interrupted so far are read: the thread is among them, and the function returns *)
    pass. meets_head.
    { apply meets_ret. intros rr _ _ Hrr Hgives rg spg Hrg. rewrite Hrr in Hrg. injection Hrg as <- _.
      exact (returned_unit N _ Hgives). }
    (* or it is not: it is interrupted, which returns *)
    step_rule. intros wint ysint Hwint _ Hysint Hmkint. apply args_one in Hysint as (ytint & -> & _).
    split; [miss |]. intros wintd rint xint Hwintd Hdoneint Hgivesint _.
    rewrite (Hinterrupt _ _ _ _ (done_by_someone Hdoneint)) in Hgivesint.
    destruct xint as [e | u]; [contradiction |].
    (* the threads interrupted are read again, and written with the thread among them; it returns *)
    pass. pass. pass. meets_head.
    apply meets_ret. intros rr _ _ Hrr Hgives rg spg Hrg. rewrite Hrr in Hrg. injection Hrg as <- _.
    exact (returned_unit N _ Hgives). }
  intros wu2 rt2 xt2 Hwu2 _ _ _. meets_head; [pass |].
  (* then the next turn *)
  apply IH; lia.
Qed.
