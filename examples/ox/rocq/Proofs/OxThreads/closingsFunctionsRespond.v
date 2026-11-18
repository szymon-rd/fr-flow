Require Export FrFlowGen.OxThreads.closingsFunctionsRespond.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.
Require FrFlow.Scala.Jdk.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree, three deep. A function closing passes to
    a traversal, run by a thread that is given its turn, applies `interruptIfNeeded`, which is responded to: it
    reads, interrupts, writes and returns. The second function then joins the thread. The thread has been
    interrupted by then; it was added to the herd's set; so it ends the function it was made for, and the join is
    responded to. Whatever the join gave, what the function does after is responded to, and it ends. *)
Lemma closingsFunctionsRespond_Proofs_complete : closingsFunctionsRespond_Obl_complete.
Proof.
  intros heldIn history [N C] Hinterrupts Hends Hjoinresp Hproceeds Happlyproceeds Hintresp Hsuppresp Hjoin Hmade
    h f x c k code made [[Htrav Haccept] Hmadetorun].
  pose proof Htrav as (from & a0 & [[Ha0 Hcalled] Hmakes]).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r0 & inside & Hh & Hcall).
  (* what the walk takes of the call: it proceeds, and so does what it applies; what it applies leaves the
     thread interrupted; and a join of the thread is responded to once the thread has been interrupted *)
  pose proof (proceeds_moves _ _ _ (Hproceeds h f x c k (conj Htrav Haccept))) as Hmoves.
  assert (forall g t a, itselfMakes history (Invocation_mk L.Function_apply [g; t]) c k a ->
    moves history c a) as Happmoves.
  { intros g t a Happ. apply proceeds_moves.
    exact (Happlyproceeds h f x c k g t a (conj (conj Htrav Haccept) Happ)). }
  assert (forall g t a r b, itselfMakes history (Invocation_mk L.Function_apply [g; t]) c k a ->
    completedBy history (Invocation_mk L.Function_apply [g; t]) c a r b ->
    exists from0 value to, to <= b /\ exists who, completedBy history
      (Invocation_mk L.Thread_interrupt [t]) who from0 (Response_Returned value) to) as Hleft.
  { intros g t a r b Happ Hdone.
    exact (Hinterrupts h f x c k g t a r b (conj (conj (conj Htrav Haccept) Happ) Hdone)). }
  assert (Def_interrupted.interrupted history x -> forall m, calledBy history
      (Invocation_mk L.Thread_join [x]) c m -> exists to, overBy history c m to) as Hjoined.
  { intros Hint m Hjoincalled.
    destruct (Hends h x code made (conj Hmadetorun Hint)) as (fy & ry & ay & by_ & iy & Hnew & Hran).
    exact (proj2 (Hjoinresp fy ry x c ay by_ iy m (conj (conj Hnew Hran) Hjoincalled))). }
  clear Hinterrupts Hends Hjoinresp Hproceeds Happlyproceeds Hmadetorun Htrav.
  revert x c k Ha0 Haccept Hmoves Happmoves Hleft Hjoined.
  pose proof (makes_direct Hmakes) as Hdirect. revert f Hmakes. revert a0 Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k0 Hargs _. apply vals_none in Hargs as ->.
  (* up to the loop, and in a turn up to the first traversal *)
  repeat pass. meets_head. apply meets_iter with (J := fun _ w _ => from < w); [| lia].
  intros tr1 wt s1 HJ IH.
  pass. pass. meets_head; [pass | repeat pass |].
  pass.
  step. intros wt1 yst1 Hwt1 _ Hyst1 Hmk1. apply args_two in Hyst1 as (yset1 & yfun1 & -> & _ & Hyfun1).
  split.
  { intros fe Hit xe ce ke Hlt Haccept Hmoves Happmoves Hleft Hjoined.
    pose proof (makes_one Hmk1 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun1 with names _ _ (VCode ?fn) =>
      assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Haccept as [[inside1 Hcall1] | (a1 & inside1 & sp1 & Hat1)];
      [| exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun1 Hwritten)].
    split; [exists inside1; exact Hcall1 |].
    refine (function_leads _ C Hcall1 eq_refl Hyfun1 Hwritten Hmoves _).
    intros args' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & Hvthread).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    (* it applies `interruptIfNeeded` to the thread *)
    lstep. intros wapp m yg ysg Hwapp Hqapp Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & Hythread).
    pose proof (one_name N _ _ _ Hythread Hvthread) as ->.
    lazymatch type of Hyg with names _ _ (VCode ?fn) =>
      assert (written Code_files fn) as Hwritteng by (apply written_function; vm_compute; reflexivity) end.
    split.
    { (* the function it applies is responded to: it reads the threads interrupted, interrupts the thread if it
         is not among them, writes it among them, and returns *)
      left.
      refine (function_leads _ C Hinv eq_refl Hyg Hwritteng (Happmoves _ _ _ (or_introl Hinv)) _).
      intros argsg Hargsg Hgiveng. apply vals_one in Hargsg as (vthreadg & -> & Hvthreadg).
      cbv beta iota delta [given] in Hgiveng. inversion Hgiveng as [| pi vi psi vsi Hthreadg _]; subst.
      typed Hthreadg.
      lstep. intros wr vheld yheld Hwr Hqr Hyheld Htyheld Hread. typed Htyheld.
      leads_head.
      { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists wZ, rZ, []; exact HeZ. }
      lstep_rule. intros wint ysint Hwint Hqint Hysint Hmkint. apply args_one in Hysint as (ytint & -> & Hytint).
      split; [intros Hinvint; destruct (Hintresp _ ce wint (conj (ex_intro _ _ Hinvint) I)) as (to & Hover);
        exact (over_responded _ _ wapp _ _ Hover) |].
      intros wintd rint xint Hwintd Hqintd Hdoneint Hgivesint Hretint.
      leads_head.
      all: try (lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists wZ, rZ, []; exact HeZ).
      lstep. intros wr2 vheld2 yheld2 Hwr2 Hqr2 Hyheld2 Htyheld2 Hread2. typed Htyheld2.
      lstep. intros wmk xmk Hwmk Hqmk Hopmk.
      lstep. intros wst xst Hwst Hqst Hopst.
      leads_head.
      all: lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists wZ, rZ, []; exact HeZ. }
    (* and ends *)
    intros wappd rapp spapp xapp Hwappd Hqappd Hrespapp Hgivesapp.
    leads_head.
    all: lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
  intros wu1 rt1 xt1 Hwu1 _ _ _. meets_head; [pass |].
  (* the second traversal: its function applies `interruptIfNeeded` too, then joins the thread *)
  pass.
  step. intros wt2 yst2 Hwt2 _ Hyst2 Hmk2. apply args_two in Hyst2 as (yset2 & yfun2 & -> & _ & Hyfun2).
  split.
  { intros fe Hit xe ce ke Hlt Haccept Hmoves Happmoves Hleft Hjoined.
    pose proof (makes_one Hmk2 Hit) as E'. injection E' as _ ->.
    lazymatch type of Hyfun2 with names _ _ (VCode ?fn) =>
      assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
    destruct Haccept as [[inside1 Hcall1] | (a1 & inside1 & sp1 & Hat1)];
      [| exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun2 Hwritten)].
    split; [exists inside1; exact Hcall1 |].
    refine (function_leads _ C Hcall1 eq_refl Hyfun2 Hwritten Hmoves _).
    intros args' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & Hvthread).
    cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
    (* it applies `interruptIfNeeded` to the thread *)
    lstep. intros wapp m yg ysg Hwapp Hqapp Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hysg as (ythread & -> & Hythread).
    pose proof (one_name N _ _ _ Hythread Hvthread) as ->.
    lazymatch type of Hyg with names _ _ (VCode ?fn) =>
      assert (written Code_files fn) as Hwritteng by (apply written_function; vm_compute; reflexivity) end.
    split.
    { (* the function it applies is responded to: it reads the threads interrupted, interrupts the thread if it
         is not among them, writes it among them, and returns *)
      left.
      refine (function_leads _ C Hinv eq_refl Hyg Hwritteng (Happmoves _ _ _ (or_introl Hinv)) _).
      intros argsg Hargsg Hgiveng. apply vals_one in Hargsg as (vthreadg & -> & Hvthreadg).
      cbv beta iota delta [given] in Hgiveng. inversion Hgiveng as [| pi vi psi vsi Hthreadg _]; subst.
      typed Hthreadg.
      lstep. intros wr vheld yheld Hwr Hqr Hyheld Htyheld Hread. typed Htyheld.
      leads_head.
      { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists wZ, rZ, []; exact HeZ. }
      lstep_rule. intros wint ysint Hwint Hqint Hysint Hmkint. apply args_one in Hysint as (ytint & -> & Hytint).
      split; [intros Hinvint; destruct (Hintresp _ ce wint (conj (ex_intro _ _ Hinvint) I)) as (to & Hover);
        exact (over_responded _ _ wapp _ _ Hover) |].
      intros wintd rint xint Hwintd Hqintd Hdoneint Hgivesint Hretint.
      leads_head.
      all: try (lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists wZ, rZ, []; exact HeZ).
      lstep. intros wr2 vheld2 yheld2 Hwr2 Hqr2 Hyheld2 Htyheld2 Hread2. typed Htyheld2.
      lstep. intros wmk xmk Hwmk Hqmk Hopmk.
      lstep. intros wst xst Hwst Hqst Hopst.
      leads_head.
      all: lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists wZ, rZ, []; exact HeZ. }
    (* the thread has been interrupted by now *)
    intros wappd rapp spapp xapp Hwappd Hqappd Hrespapp Hgivesapp.
    assert (Def_interrupted.interrupted history xe) as Hint.
    { destruct (Hleft yg xe wapp rapp (wappd + 1) (or_introl Hinv)) as (fQ & vQ & toQ & HtoQ & HcQ).
      - right. split; [exists (Some ke); exact Hinv |]. exists spapp.
        replace (wappd + 1 - 1) with wappd by lia. exact Hrespapp.
      - exists (wappd + 1), fQ, vQ, toQ. split; [exact HtoQ | exact HcQ]. }
    leads_head.
    all: try (lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ])).
    (* it joins the thread: the join is responded to, the thread ending the function it was made for *)
    lstep_rule. intros wj ysj Hwj Hqj Hysj Hmkj. apply args_one in Hysj as (ytj & -> & Hytj).
    pose proof (one_name N _ _ _ Hytj Hvthread) as ->.
    split.
    { intros Hinvj. destruct (Hjoined Hint wj (or_introl (ex_intro _ _ Hinvj))) as (to & Hover).
      exact (over_responded _ _ ke _ _ Hover). }
    intros wjd rj xj Hwjd Hqjd Hdonej Hgivesj Hretj.
    destruct (Hjoin _ _ _ _ (done_by_someone Hdonej)) as [-> | ->].
    { destruct xj as [e | u]; [contradiction |]. leads_head.
      lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
    destruct xj as [e | u]; [| contradiction]. apply threw_interruption in Hgivesj as ->.
    (* it threw an interruption, which is caught: the variable of what interrupted closing is read *)
    lstep. intros wre vre yre Hwre Hqre Hyre Htyre Hreade.
    leads_head.
    (* it holds none: the interruption is written there, and the function ends *)
    1, 2: lstep_rule; intros wmk xmk Hwmk Hqmk Hopmk; lstep; intros wst xst Hwst Hqst Hopst; leads_head;
      lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]).
    (* it holds one: it is read again, and the interruption added to it *)
    lstep_rule. intros wre2 vre2 yre2 Hwre2 Hqre2 Hyre2 Htyre2 Hreade2.
    leads_head.
    all: lstep_rule; intros wsu yssu Hwsu Hqsu Hyssu Hmksu.
    all: try (match goal with E : Jdk.as_exn ?v = Some _ |- _ =>
      assert (receiver v = [v]) as Hrec by (destruct v as [| | | | o | |]; try discriminate E; try reflexivity;
        destruct o; try discriminate E; reflexivity); rewrite Hrec in Hyssu end).
    all: cbn in Hyssu; apply args_two in Hyssu as (ysA & ysB & -> & _ & _).
    all: (split; [intros Hinvsu; destruct (Hsuppresp ysA ysB ce wsu (conj (ex_intro _ _ Hinvsu) I)) as (to & Hover);
      exact (over_responded _ _ ke _ _ Hover) |]).
    all: intros wsud rsu xsu Hwsud Hqsud Hdonesu Hgivessu Hretsu; leads_head.
    all: lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
  intros wu2 rt2 xt2 Hwu2 _ _ _. meets_head; [pass |].
  (* then the next turn *)
  apply IH; lia.
Qed.
