Require Export FrFlowGen.OxThreads.closingsFunctionsReturn.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

Lemma closingsFunctionsReturn_Proofs_complete : closingsFunctionsReturn_Obl_complete.
Proof.
  intros heldIn history [N C] Happly Hkeeps Hjoin Hsuppressed Hone Hmade h f x c k r b
    [(from & a0 & [[Ha0 Hcalled] Hmakes]) Hdone].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r0 & inside & Hh & Hcall).
  revert x c k r b Ha0 Hdone.
  pose proof (makes_direct Hmakes) as Hdirect. revert f Hmakes. revert a0 Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k0 Hargs _. apply vals_none in Hargs as ->.
  (* the owner is checked and the flag set; the variable is made, by the caller, in this call *)
  pass. pass. pass. pass.
  step. intros wvar xvar Hwvar _ Hmadevar. cbn [op_event] in Hmadevar.
  destruct Hmadevar as (rvar & yvar & hsvar & -> & Hclassvar & Hyvar & Hholding & Hevar).
  split; [miss |].
  (* in a turn, up to the first traversal *)
  meets_head. apply meets_iter with (J := fun _ w _ => wvar < w); [| lia].
  intros tr1 wt s1 HJ IH.
  pass. pass. meets_head; [pass | repeat pass |].
  (* the first traversal: its function applies `interruptIfNeeded`, which returns, and no more *)
  pass.
  step. intros wt1 yst1 Hwt1 _ Hyst1 Hmk1. apply args_two in Hyst1 as (yset1 & yfun1 & -> & _ & Hyfun1).
  split.
  { intros fe Hit xe ce ke re be Hlt Hdone.
    pose proof (makes_one Hmk1 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun1 with names _ _ (VCode ?fn) =>
      assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Hdone as [[(ins1 & sp1 & Hat1) _] | [[inside1 Hcall1] [sp1 Hend1]]];
      [exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun1 Hwritten) |].
    assert (direct ce ke (history (be - 1))) as Hdir1 by (rewrite Hend1; cbn; auto).
    revert re sp1 Hend1. revert Hdir1. generalize (be - 1).
    refine (function_meets _ C Hcall1 eq_refl Hyfun1 Hwritten _).
    intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & _).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & _).
    split; [miss |]. intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp.
    assert (rapp = Response_Returned Value_Unit_) as ->.
    { apply (Happly h fe xe ce ke yg ythread wapp rapp (wappd + 1)).
      split; [split; [split |] |].
      - exists from, wt1. split; [split; [exact Hlt | exact Hcalled] | exact Hit].
      - left. exists inside1. exact Hcall1.
      - left. exact Hinv.
      - right. split; [exists (Some ke); exact Hinv |]. exists spapp.
        replace (wappd + 1 - 1) with wappd by lia. exact Hrespapp. }
    destruct xapp as [e | u]; [contradiction |].
    pose proof (names_one N Value_Unit_ u VUnit Hgivesapp (of_unit N)) as ->.
    meets_head. apply meets_ret. intros rr _ _ Hrr Hgives re sp1 Hre. rewrite Hrr in Hre. injection Hre as <- _.
    exact (returned_unit N _ Hgives). }
  intros wu1 rt1 xt1 Hwu1 _ _ _. meets_head; [pass |].
  (* the second: its function applies it, then joins the thread *)
  pass.
  step. intros wt2 yst2 Hwt2 _ Hyst2 Hmk2. apply args_two in Hyst2 as (yset2 & yfun2 & -> & _ & Hyfun2).
  split.
  { intros fe Hit xe ce ke re be Hlt Hdone.
    pose proof (makes_one Hmk2 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun2 with names _ _ (VCode ?fn) =>
      assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Hdone as [[(ins1 & sp1 & Hat1) _] | [[inside1 Hcall1] [sp1 Hend1]]];
      [exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun2 Hwritten) |].
    assert (direct ce ke (history (be - 1))) as Hdir1 by (rewrite Hend1; cbn; auto).
    revert re sp1 Hend1. revert Hdir1. generalize (be - 1).
    refine (function_meets _ C Hcall1 eq_refl Hyfun2 Hwritten _).
    intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & _).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & _).
    split; [miss |]. intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp.
    assert (rapp = Response_Returned Value_Unit_) as ->.
    { apply (Happly h fe xe ce ke yg ythread wapp rapp (wappd + 1)).
      split; [split; [split |] |].
      - exists from, wt2. split; [split; [exact Hlt | exact Hcalled] | exact Hit].
      - left. exists inside1. exact Hcall1.
      - left. exact Hinv.
      - right. split; [exists (Some ke); exact Hinv |]. exists spapp.
        replace (wappd + 1 - 1) with wappd by lia. exact Hrespapp. }
    destruct xapp as [e | u]; [contradiction |].
    pose proof (names_one N Value_Unit_ u VUnit Hgivesapp (of_unit N)) as ->.
    (* then it joins the thread: that returns, or throws an interruption, which the function catches *)
    step. intros wj ysj Hwj _ Hysj Hmkj. apply args_one in Hysj as (ytj & -> & _). split; [miss |].
    intros wjd rj xj Hwjd Hdonej Hgivesj _.
    destruct (Hjoin _ _ _ _ (done_by_someone Hdonej)) as [-> | ->].
    { destruct xj as [e | u']; [contradiction |].
      pose proof (names_one N Value_Unit_ u' VUnit Hgivesj (of_unit N)) as ->. meets_head.
      apply meets_ret. intros rr _ _ Hrr Hgives re sp1 Hre. rewrite Hrr in Hre. injection Hre as <- _.
      exact (returned_unit N _ Hgives). }
    destruct xj as [e | u']; [| contradiction]. apply threw_interruption in Hgivesj as ->.
    (* the variable is read: by closing's caller, who alone touches it *)
    step. intros wread1 held1 yheld1 Hwread1 Hpast1 Hyheld1 Htyheld1 Hread1. split; [miss |].
    assert (ce = heldIn L.ThreadHerd_herdOwner h) as Hce.
    { apply (Hkeeps h _ from yvar ce wread1).
      split; [split; [split; [exists inside; exact Hcall | exact I] | unfold itselfCreates; eauto] |].
      unfold touches. eauto 7. }
    meets_head.
    (* it holds none: it is written, and the function returns *)
    1, 2: pass; pass; meets_head; apply meets_ret; intros rr _ _ Hrr Hgives re sp1 Hre; rewrite Hrr in Hre;
      injection Hre as <- _; exact (returned_unit N _ Hgives).
    (* it holds an exception: it is read again, and the second read finds what the first did *)
    step. intros wread2 held2 yheld2 Hwread2 Hpast2 Hyheld2 Htyheld2 Hread2. split; [miss |].
    assert (yheld1 = yheld2) as Hsame.
    { refine (reads_agree C Hread1 Hread2 ltac:(lia) Hyvar eq_refl _ _ _).
      - intros km bm insm clsm hsm Hm. pose proof (made_at_one C Hm Hevar) as ->.
        rewrite Hevar in Hm. injection Hm as <- _ _ _. symmetry. exact Hce.
      - intros kw bw insw fw yw Hw. rewrite Hce. apply (Hkeeps h _ from yvar bw kw).
        split; [split; [split; [exists inside; exact Hcall | exact I] | unfold itselfCreates; eauto] |].
        unfold touches. eauto 7.
      - intros kw insw yw Hafter Hbefore Hw.
        assert (insw = Some ke) as ->.
        { refine (written_itself history ce _ ke insw _ _ _ kw (Hone ce) ltac:(lia)
            (ex_intro _ inside1 Hcall1) _ Hw _).
          - intros (kr & ar & spr & Hkr & Hresp).
            refine (function_over C Hcall1 eq_refl Hyfun2 Hwritten Hresp (w := wread2) ltac:(lia) _).
            rewrite Hread2. cbn. auto.
          - intros between m Hkm Hmk Hinvoke.
            assert (In m [wread1; wj; wapp]) as Hin by (apply Hpast2; [lia | rewrite Hinvoke; cbn; auto]).
            cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]].
            + rewrite Hread1 in Hinvoke. discriminate Hinvoke.
            + destruct Hdonej as [(spj & Hatj & _) | (_ & _ & spj & Hrespj)];
                [rewrite Hatj in Hinvoke; discriminate Hinvoke |].
              exists (wjd - 1). do 2 eexists. split; [lia | exact Hrespj].
            + exists wappd. do 2 eexists. split; [lia | exact Hrespapp]. }
        assert (In kw [wread1; wj; wapp]) as Hin by (apply Hpast2; [lia | rewrite Hw; cbn; auto]).
        cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; lia. }
    subst yheld2. pose proof (names_one N _ _ _ Hyheld1 Hyheld2) as <-.
    meets_head.
    { match goal with Hnone : Jdk.as_exn (VObj Null) = Some _ |- _ => vm_compute in Hnone; discriminate Hnone end. }
    (* what was caught is added to it, which returns; and the function returns *)
    step_rule. intros wsup yssup Hwsup _ Hyssup Hmksup. split; [miss |].
    intros wsupd rsup xsup Hwsupd Hdonesup Hgivessup _.
    assert (receiver held1 = [held1] /\ held1 <> vnull) as [Hrecv Hnotnull].
    { match goal with Hexn : Jdk.as_exn held1 = Some _ |- _ => revert Hexn end. clear.
      destruct held1 as [| | | | o | |]; intros Hexn; try discriminate Hexn.
      all: try (split; [reflexivity | discriminate]).
      destruct o; try discriminate Hexn; split; [reflexivity | discriminate]. }
    rewrite Hrecv in Hyssup. cbn in Hyssup. apply args_two in Hyssup as (yrecv & yexn & -> & Hyrecv & Hyexn).
    pose proof (one_name N _ _ _ Hyrecv Hyheld1) as ->.
    pose proof (one_name N _ _ _ Hyexn (of_thrown N "java.lang.InterruptedException")) as ->.
    assert (yheld1 <> Value_Null) as Hheld.
    { intros ->. apply Hnotnull. exact (names_one N _ _ _ Hyheld1 (of_null N)). }
    rewrite (Hsuppressed yheld1 Hheld _ _ _ (done_by_someone Hdonesup)) in Hgivessup.
    destruct xsup as [e' | u'']; [contradiction |].
    pose proof (names_one N Value_Unit_ u'' VUnit Hgivessup (of_unit N)) as ->.
    meets_head. apply meets_ret. intros rr _ _ Hrr Hgives re sp1 Hre. rewrite Hrr in Hre. injection Hre as <- _.
    exact (returned_unit N _ Hgives). }
  intros wu2 rt2 xt2 Hwu2 _ _ _. meets_head; [pass |].
  (* then the next turn *)
  apply IH; lia.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
