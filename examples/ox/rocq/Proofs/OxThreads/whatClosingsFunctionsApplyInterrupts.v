Require Export FrFlowGen.OxThreads.whatClosingsFunctionsApplyInterrupts.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree, three deep, with what holds of the variable
    closing keeps the threads it has interrupted in: every set written there holds only threads that have been
    interrupted. `interruptIfNeeded` reads the variable; a thread it finds there has been interrupted, by what
    holds of what was last written; one it does not find, it interrupts, and writes among them. *)
Lemma whatClosingsFunctionsApplyInterrupts_Proofs_complete : whatClosingsFunctionsApplyInterrupts_Obl_complete.
Proof.
  intros heldIn history [N C] Hkeeps Hwriters Hjoin Hinterrupt Hmade.
  pose (owner := fun h : Value => heldIn L.ThreadHerd_herdOwner h).
  pose (closing := fun h : Value =>
    Invocation_mk L.ThreadHerd_interruptAllAndJoinUntilCompleted [h]).
  (* the thread has been interrupted by the moment; a set holds only such threads; the variable is one a call of
     closing made *)
  pose (Interrupted := fun (t : Value) (k : Z) => exists from value to, to <= k /\ exists who,
    completedBy history (Invocation_mk L.Thread_interrupt [t]) who from
      (Response_Returned value) to).
  pose (SetInv := fun (y : Value) (k : Z) => forall xs, names N y (vdata c_set [VList xs]) ->
    forall vt, In vt xs -> exists t, names N t vt /\ Interrupted t k).
  pose (Cell := fun yo : Value => exists h from,
    calledBy history (closing h) (owner h) from /\ itselfCreates history yo (owner h) from).
  assert (forall h from, calledBy history (closing h) (owner h) from ->
    forall j, direct (owner h) from (history j) ->
    forall fe, itselfMakes history (Invocation_mk
      L.KeySetView_forEach
      [heldIn L.ThreadHerd_threads h; fe]) (owner h) from j ->
    forall xe ce ke, j < ke ->
    calledBy history (Invocation_mk L.Consumer_accept [fe; xe]) ce ke ->
    forall w, direct ce ke (history w) ->
      (forall ins yo fld y, history w = Event_Write ce ins yo fld y ->
         forall xs, ~ names N y (vdata c_set [VList xs])) /\
      (forall ge te, itselfMakes history (Invocation_mk L.Function_apply [ge; te]) ce ke w ->
         history w = Event_Invoke ce (Some ke) (Invocation_mk L.Function_apply [ge; te]) /\
         forall v, direct ce w (history v) ->
           (forall ins yo fld y, history v = Event_Write ce ins yo fld y ->
              (exists mk b' ins' cls' hs', mk < v /\ history mk = Event_Make b' ins' yo cls' hs') /\
              ((forall k' b' ins' fld' y', k' < v -> history k' = Event_Write b' ins' yo fld' y' -> SetInv y' k') ->
               SetInv y v)) /\
           (forall r sp, history v = Event_Respond ce w r sp ->
              (forall yo k' b' ins' fld' y', k' < v -> history k' = Event_Write b' ins' yo fld' y' -> Cell yo ->
                 SetInv y' k') ->
              Interrupted te (v + 1)))) as Hwalk.
  { intros h from Hcalled.
    destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
      (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r0 & inside & Hh & Hcall).
    refine (method_meets _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") Hcall Hh eq_refl _).
    intros args k0 Hargs _. apply vals_none in Hargs as ->.
    (* the owner is checked and the flag set; the variable of the threads interrupted is made, in this call *)
    pass. pass. pass. meets_head; [pass |].
    step_rule. intros wvar xvar Hwvar _ Hmadevar. cbn [op_event] in Hmadevar.
    destruct Hmadevar as (rvar & yvar & hsvar & -> & Hclassvar & Hyvar & Hholding & Hevar).
    split; [miss |].
    (* it holds no thread, when made *)
    assert (forall fldQ yQ, hsvar = [Held_mk fldQ yQ] -> names N yQ (vdata c_set [VList []])) as Hfirst.
    { intros fldQ yQ ->. inversion Hholding as [| fv hv fvs hvs [_ Hheld] _]; subst. exact Hheld. }
    (* the other variable; then in a turn, up to the first traversal *)
    pass. meets_head. apply meets_iter with (J := fun _ w _ => wvar < w); [| lia].
    intros tr1 wt s1 HJ IH.
    pass. pass. meets_head; [pass | repeat pass |].
    pass.
    step. intros wt1 yst1 Hwt1 _ Hyst1 Hmk1. apply args_two in Hyst1 as (yset1 & yfun1 & -> & _ & Hyfun1).
    split.
    { intros fe Hit xe ce ke Hlt Haccept.
      pose proof (makes_one Hmk1 Hit) as E'. injection E' as _ ->.
      lazymatch type of Hyfun1 with names _ _ (VCode ?fn) =>
        assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
      destruct Haccept as [[inside1 Hcall1] | (a1 & inside1 & sp1 & Hat1)];
        [| exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun1 Hwritten)].
      refine (function_meets _ C Hcall1 eq_refl Hyfun1 Hwritten _).
      intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & _).
      cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
      (* it applies `interruptIfNeeded` to the thread *)
      step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
      apply args_one in Hysg as (ythread & -> & Hythread).
      split; [| intros; repeat pass].
      split; [intros insQ yoQ fldQ yQ HwQ; rewrite Hinv in HwQ; discriminate HwQ |].
      intros gg tg Hitg. pose proof (makes_one (or_introl Hinv) Hitg) as Eg. injection Eg as -> ->.
      split; [exact Hinv |].
      lazymatch type of Hyg with names _ _ (VCode ?fn) =>
        assert (written Code_files fn) as Hwritteng by (apply written_function; vm_compute; reflexivity) end.
      refine (function_meets _ C Hinv eq_refl Hyg Hwritteng _).
      intros argsg kg Hargsg Hgiveng. apply vals_one in Hargsg as (vthreadg & -> & Hvthreadg).
      cbv beta iota delta [given] in Hgiveng. inversion Hgiveng as [| pi vi psi vsi Hthreadg _]; subst.
      typed Hthreadg.
      (* the threads interrupted so far are read *)
      step. intros wr vheld yheld Hwr Hpastr Hyheld Htyheld Hread. split; [miss |].
      (* by closing's caller, who alone touches the variable: so what is read is what was last written there,
         or what the variable was made holding *)
      assert (ce = owner h) as Hce.
      { apply (Hkeeps h (owner h) from yvar ce wr).
        split; [split; [split; [exists inside; exact Hcall | exact I] | exists wvar; eauto] |].
        unfold touches. eauto 7. }
      assert ((exists kw insw, kw < wr /\ history kw = Event_Write ce insw yvar
          (field_label Code_table "<var>:scala.collection.immutable.Set" "value") yheld) \/
        names N yheld (vdata c_set [VList []])) as Hfound.
      { destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 C)))))) _ _ _ _ _ _ _ _ Hread Hyvar eq_refl)
          as [(kw & insw & Hkw & Hw & _) | [_ (km & bm & insm & clsm & Hm)]].
        - intros km bm insm clsm hsm Hm. pose proof (made_at_one C Hm Hevar) as ->.
          rewrite Hevar in Hm. injection Hm as <- _ _ _. symmetry. exact Hce.
        - intros kw bw insw fw yw Hw. rewrite Hce. apply (Hkeeps h (owner h) from yvar bw kw).
          split; [split; [split; [exists inside; exact Hcall | exact I] | exists wvar; eauto] |].
          unfold touches. eauto 7.
        - left. eauto.
        - right. pose proof (made_at_one C Hm Hevar) as ->. rewrite Hevar in Hm. injection Hm as _ _ _ Ehs.
          exact (Hfirst _ _ Ehs). }
      typed Htyheld.
      meets_head.
      (* it is among them: it has been interrupted, by what holds of what was last written there *)
      { apply meets_ret. intros rr Hk Hpastret Hrr Hgives. split.
        { intros insQ yoQ fldQ yQ HwQ. rewrite Hrr in HwQ. discriminate HwQ. }
        intros rQ spQ _ Hall.
        assert (In vthreadg b) as Hin.
        { unfold some_of in E. apply existsb_exists in E as (vx & Hvx & Evx). apply val_eqb_eq in Evx. subst vx.
          exact Hvx. }
        destruct Hfound as [(kw & insw & Hkw & Hw) | Hnone].
        - assert (Cell yvar) as Hcell by (exists h, from; split; [exact Hcalled | exists wvar; eauto]).
          destruct (Hall yvar kw ce insw _ yheld ltac:(lia) Hw Hcell b Hyheld vthreadg Hin)
            as (tQ & HtQ & (fQ & vQ & toQ & HtoQ & HcQ)).
          pose proof (one_name N _ _ _ HtQ Hvthreadg) as ->. exists fQ, vQ, toQ. split; [lia | exact HcQ].
        - pose proof (names_one N _ _ _ Hyheld Hnone) as Eb. injection Eb as ->. destruct Hin. }
      (* or it is not: it is interrupted, which returns *)
      step_rule. intros wint ysint Hwint _ Hysint Hmkint. apply args_one in Hysint as (ytint & -> & Hytint).
      pose proof (one_name N _ _ _ Hytint Hvthreadg) as ->.
      split; [split; [intros insQ yoQ fldQ yQ HwQ; revert HwQ; miss | intros rQ spQ HrQ; revert HrQ; miss] |].
      intros wintd rint xint Hwintd Hdoneint Hgivesint _.
      rewrite (Hinterrupt _ _ _ _ (done_by_someone Hdoneint)) in Hgivesint.
      destruct xint as [e | u]; [contradiction |].
      assert (Interrupted tg wintd) as Hnow.
      { exists wint, Value_Unit_, wintd. split; [lia |]. exists ce.
        rewrite (Hinterrupt _ _ _ _ (done_by_someone Hdoneint)) in Hdoneint. exact (done_completed Hdoneint). }
      (* the threads interrupted are read again *)
      step. intros wr2 vheld2 yheld2 Hwr2 Hpastr2 Hyheld2 Htyheld2 Hread2. split; [miss |].
      assert ((exists kw insw, kw < wr2 /\ history kw = Event_Write ce insw yvar
          (field_label Code_table "<var>:scala.collection.immutable.Set" "value") yheld2) \/
        names N yheld2 (vdata c_set [VList []])) as Hfound2.
      { destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 C)))))) _ _ _ _ _ _ _ _ Hread2 Hyvar eq_refl)
          as [(kw & insw & Hkw & Hw & _) | [_ (km & bm & insm & clsm & Hm)]].
        - intros km bm insm clsm hsm Hm. pose proof (made_at_one C Hm Hevar) as ->.
          rewrite Hevar in Hm. injection Hm as <- _ _ _. symmetry. exact Hce.
        - intros kw bw insw fw yw Hw. rewrite Hce. apply (Hkeeps h (owner h) from yvar bw kw).
          split; [split; [split; [exists inside; exact Hcall | exact I] | exists wvar; eauto] |].
          unfold touches. eauto 7.
        - left. eauto.
        - right. pose proof (made_at_one C Hm Hevar) as ->. rewrite Hevar in Hm. injection Hm as _ _ _ Ehs.
          exact (Hfirst _ _ Ehs). }
      typed Htyheld2.
      (* and written with the thread among them: every thread of the set written has been interrupted *)
      pass. meets_head.
      step_rule. intros ww xw Hww Hpastw Hopw. cbn [op_event] in Hopw.
      destruct Hopw as (yow & yw & -> & Hatw & Hyw & Hevw). destruct (read_place Hyvar Hatw) as [-> _].
      split; [split; [| intros rQ spQ HrQ; rewrite Hevw in HrQ; discriminate HrQ] |].
      { intros insQ yoQ fldQ yQ HwQ. rewrite Hevw in HwQ. injection HwQ as _ <- _ <-.
        split; [exists wvar, (owner h), (Some from), "<var>:scala.collection.immutable.Set"%string, hsvar;
          split; [lia | exact Hevar] |].
        intros Hprev xsQ HxsQ vt HinQ. pose proof (names_one N _ _ _ Hyw HxsQ) as Ev.
        assert (In vt b0 \/ vt = vthreadg) as [Hold | ->].
        { revert Ev. destruct (some_of _ b0); intros Ev; injection Ev as <-; [left; exact HinQ |].
          apply in_app_or in HinQ as [HinQ | [<- | []]]; [left; exact HinQ | right; reflexivity]. }
        - destruct Hfound2 as [(kw & insw & Hkw & Hw) | Hnone].
          + destruct (Hprev kw ce insw _ yheld2 ltac:(lia) Hw b0 Hyheld2 vt Hold)
              as (tQ & HtQ & (fQ & vQ & toQ & HtoQ & HcQ)).
            exists tQ. split; [exact HtQ | exists fQ, vQ, toQ; split; [lia | exact HcQ]].
          + pose proof (names_one N _ _ _ Hyheld2 Hnone) as Eb. injection Eb as ->. destruct Hold.
        - exists tg. split; [exact Hvthreadg |]. destruct Hnow as (fQ & vQ & toQ & HtoQ & HcQ).
          exists fQ, vQ, toQ. split; [lia | exact HcQ]. }
      (* and it returns *)
      intros. meets_head. apply meets_ret. intros rr Hk Hpastret Hrr Hgives. split;
        [intros insQ yoQ fldQ yQ HwQ; rewrite Hrr in HwQ; discriminate HwQ |].
      intros rQ spQ _ _. destruct Hnow as (fQ & vQ & toQ & HtoQ & HcQ). exists fQ, vQ, toQ.
      split; [lia | exact HcQ]. }
    intros wu1 rt1 xt1 Hwu1 _ _ _. meets_head; [pass |].
    (* the second traversal: its function applies `interruptIfNeeded` too, then joins the thread *)
    pass.
    step. intros wt2 yst2 Hwt2 _ Hyst2 Hmk2. apply args_two in Hyst2 as (yset2 & yfun2 & -> & _ & Hyfun2).
    split.
    { intros fe Hit xe ce ke Hlt Haccept.
      pose proof (makes_one Hmk2 Hit) as E'. injection E' as _ ->.
      lazymatch type of Hyfun2 with names _ _ (VCode ?fn) =>
        assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
      destruct Haccept as [[inside1 Hcall1] | (a1 & inside1 & sp1 & Hat1)];
        [| exfalso; exact (function_not_atomic C Hat1 eq_refl Hyfun2 Hwritten)].
      refine (function_meets _ C Hcall1 eq_refl Hyfun2 Hwritten _).
      intros args' k' Hargs' Hgiven. apply vals_one in Hargs' as (vthread & -> & _).
      cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hthread _]; subst. typed Hthread.
      step. intros wapp m yg ysg Hwapp _ Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
      apply args_one in Hysg as (ythread & -> & Hythread).
      split.
      2: { (* then it joins the thread: that returns, or throws an interruption, which the function catches *)
        intros wappd rapp spapp xapp Hwappd _ _. meets_head; [pass |].
        step_rule. intros wj ysj Hwj _ Hysj Hmkj. apply args_one in Hysj as (ytj & -> & _). split; [miss |].
        intros wjd rj xj Hwjd Hdonej Hgivesj _.
        destruct (Hjoin _ _ _ _ (done_by_someone Hdonej)) as [-> | ->].
        { destruct xj as [e | u]; [contradiction |]. repeat pass. }
        destruct xj as [e | u]; [| contradiction]. apply threw_interruption in Hgivesj as ->.
        repeat pass.
        (* it holds none yet: the interruption is written there, which is no set of threads *)
        all: step; intros we xev Hwe _ Hope; cbn [op_event] in Hope.
        all: destruct Hope as (yoe & ye & -> & _ & Hye & Heve).
        all: (split; [split; [intros insQ yoQ fldQ yQ HwQ xsQ HxsQ; rewrite Heve in HwQ; injection HwQ as _ _ _ <-;
            pose proof (names_one N _ _ _ Hye HxsQ) as Ex; discriminate Ex
          | intros gQ tQ HQ; revert HQ; miss] |]).
        all: intros; repeat pass. }
      split; [intros insQ yoQ fldQ yQ HwQ; rewrite Hinv in HwQ; discriminate HwQ |].
      intros gg tg Hitg. pose proof (makes_one (or_introl Hinv) Hitg) as Eg. injection Eg as -> ->.
      split; [exact Hinv |].
      lazymatch type of Hyg with names _ _ (VCode ?fn) =>
        assert (written Code_files fn) as Hwritteng by (apply written_function; vm_compute; reflexivity) end.
      refine (function_meets _ C Hinv eq_refl Hyg Hwritteng _).
      intros argsg kg Hargsg Hgiveng. apply vals_one in Hargsg as (vthreadg & -> & Hvthreadg).
      cbv beta iota delta [given] in Hgiveng. inversion Hgiveng as [| pi vi psi vsi Hthreadg _]; subst.
      typed Hthreadg.
      (* the threads interrupted so far are read *)
      step. intros wr vheld yheld Hwr Hpastr Hyheld Htyheld Hread. split; [miss |].
      (* by closing's caller, who alone touches the variable: so what is read is what was last written there,
         or what the variable was made holding *)
      assert (ce = owner h) as Hce.
      { apply (Hkeeps h (owner h) from yvar ce wr).
        split; [split; [split; [exists inside; exact Hcall | exact I] | exists wvar; eauto] |].
        unfold touches. eauto 7. }
      assert ((exists kw insw, kw < wr /\ history kw = Event_Write ce insw yvar
          (field_label Code_table "<var>:scala.collection.immutable.Set" "value") yheld) \/
        names N yheld (vdata c_set [VList []])) as Hfound.
      { destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 C)))))) _ _ _ _ _ _ _ _ Hread Hyvar eq_refl)
          as [(kw & insw & Hkw & Hw & _) | [_ (km & bm & insm & clsm & Hm)]].
        - intros km bm insm clsm hsm Hm. pose proof (made_at_one C Hm Hevar) as ->.
          rewrite Hevar in Hm. injection Hm as <- _ _ _. symmetry. exact Hce.
        - intros kw bw insw fw yw Hw. rewrite Hce. apply (Hkeeps h (owner h) from yvar bw kw).
          split; [split; [split; [exists inside; exact Hcall | exact I] | exists wvar; eauto] |].
          unfold touches. eauto 7.
        - left. eauto.
        - right. pose proof (made_at_one C Hm Hevar) as ->. rewrite Hevar in Hm. injection Hm as _ _ _ Ehs.
          exact (Hfirst _ _ Ehs). }
      typed Htyheld.
      meets_head.
      (* it is among them: it has been interrupted, by what holds of what was last written there *)
      { apply meets_ret. intros rr Hk Hpastret Hrr Hgives. split.
        { intros insQ yoQ fldQ yQ HwQ. rewrite Hrr in HwQ. discriminate HwQ. }
        intros rQ spQ _ Hall.
        assert (In vthreadg b) as Hin.
        { unfold some_of in E. apply existsb_exists in E as (vx & Hvx & Evx). apply val_eqb_eq in Evx. subst vx.
          exact Hvx. }
        destruct Hfound as [(kw & insw & Hkw & Hw) | Hnone].
        - assert (Cell yvar) as Hcell by (exists h, from; split; [exact Hcalled | exists wvar; eauto]).
          destruct (Hall yvar kw ce insw _ yheld ltac:(lia) Hw Hcell b Hyheld vthreadg Hin)
            as (tQ & HtQ & (fQ & vQ & toQ & HtoQ & HcQ)).
          pose proof (one_name N _ _ _ HtQ Hvthreadg) as ->. exists fQ, vQ, toQ. split; [lia | exact HcQ].
        - pose proof (names_one N _ _ _ Hyheld Hnone) as Eb. injection Eb as ->. destruct Hin. }
      (* or it is not: it is interrupted, which returns *)
      step_rule. intros wint ysint Hwint _ Hysint Hmkint. apply args_one in Hysint as (ytint & -> & Hytint).
      pose proof (one_name N _ _ _ Hytint Hvthreadg) as ->.
      split; [split; [intros insQ yoQ fldQ yQ HwQ; revert HwQ; miss | intros rQ spQ HrQ; revert HrQ; miss] |].
      intros wintd rint xint Hwintd Hdoneint Hgivesint _.
      rewrite (Hinterrupt _ _ _ _ (done_by_someone Hdoneint)) in Hgivesint.
      destruct xint as [e | u]; [contradiction |].
      assert (Interrupted tg wintd) as Hnow.
      { exists wint, Value_Unit_, wintd. split; [lia |]. exists ce.
        rewrite (Hinterrupt _ _ _ _ (done_by_someone Hdoneint)) in Hdoneint. exact (done_completed Hdoneint). }
      (* the threads interrupted are read again *)
      step. intros wr2 vheld2 yheld2 Hwr2 Hpastr2 Hyheld2 Htyheld2 Hread2. split; [miss |].
      assert ((exists kw insw, kw < wr2 /\ history kw = Event_Write ce insw yvar
          (field_label Code_table "<var>:scala.collection.immutable.Set" "value") yheld2) \/
        names N yheld2 (vdata c_set [VList []])) as Hfound2.
      { destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 C)))))) _ _ _ _ _ _ _ _ Hread2 Hyvar eq_refl)
          as [(kw & insw & Hkw & Hw & _) | [_ (km & bm & insm & clsm & Hm)]].
        - intros km bm insm clsm hsm Hm. pose proof (made_at_one C Hm Hevar) as ->.
          rewrite Hevar in Hm. injection Hm as <- _ _ _. symmetry. exact Hce.
        - intros kw bw insw fw yw Hw. rewrite Hce. apply (Hkeeps h (owner h) from yvar bw kw).
          split; [split; [split; [exists inside; exact Hcall | exact I] | exists wvar; eauto] |].
          unfold touches. eauto 7.
        - left. eauto.
        - right. pose proof (made_at_one C Hm Hevar) as ->. rewrite Hevar in Hm. injection Hm as _ _ _ Ehs.
          exact (Hfirst _ _ Ehs). }
      typed Htyheld2.
      (* and written with the thread among them: every thread of the set written has been interrupted *)
      pass. meets_head.
      step_rule. intros ww xw Hww Hpastw Hopw. cbn [op_event] in Hopw.
      destruct Hopw as (yow & yw & -> & Hatw & Hyw & Hevw). destruct (read_place Hyvar Hatw) as [-> _].
      split; [split; [| intros rQ spQ HrQ; rewrite Hevw in HrQ; discriminate HrQ] |].
      { intros insQ yoQ fldQ yQ HwQ. rewrite Hevw in HwQ. injection HwQ as _ <- _ <-.
        split; [exists wvar, (owner h), (Some from), "<var>:scala.collection.immutable.Set"%string, hsvar;
          split; [lia | exact Hevar] |].
        intros Hprev xsQ HxsQ vt HinQ. pose proof (names_one N _ _ _ Hyw HxsQ) as Ev.
        assert (In vt b0 \/ vt = vthreadg) as [Hold | ->].
        { revert Ev. destruct (some_of _ b0); intros Ev; injection Ev as <-; [left; exact HinQ |].
          apply in_app_or in HinQ as [HinQ | [<- | []]]; [left; exact HinQ | right; reflexivity]. }
        - destruct Hfound2 as [(kw & insw & Hkw & Hw) | Hnone].
          + destruct (Hprev kw ce insw _ yheld2 ltac:(lia) Hw b0 Hyheld2 vt Hold)
              as (tQ & HtQ & (fQ & vQ & toQ & HtoQ & HcQ)).
            exists tQ. split; [exact HtQ | exists fQ, vQ, toQ; split; [lia | exact HcQ]].
          + pose proof (names_one N _ _ _ Hyheld2 Hnone) as Eb. injection Eb as ->. destruct Hold.
        - exists tg. split; [exact Hvthreadg |]. destruct Hnow as (fQ & vQ & toQ & HtoQ & HcQ).
          exists fQ, vQ, toQ. split; [lia | exact HcQ]. }
      (* and it returns *)
      intros. meets_head. apply meets_ret. intros rr Hk Hpastret Hrr Hgives. split;
        [intros insQ yoQ fldQ yQ HwQ; rewrite Hrr in HwQ; discriminate HwQ |].
      intros rQ spQ _ _. destruct Hnow as (fQ & vQ & toQ & HtoQ & HcQ). exists fQ, vQ, toQ.
      split; [lia | exact HcQ]. }
    intros wu2 rt2 xt2 Hwu2 _ _ _. meets_head; [pass |].
    (* then the next turn *)
    apply IH; lia. }
  (* so every set written to a variable closing made holds only threads that have been interrupted: a write
     comes after the variable is made, and what it writes is what was last written, with one more *)
  assert (forall yo, Cell yo -> forall k b ins fld y, history k = Event_Write b ins yo fld y -> SetInv y k)
    as Hinv.
  { intros yo (h0 & from0 & Hcalled0 & (m0 & cls0 & hs0 & Hmake0)).
    destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
      (Hmade h0 from0 ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled0) as (r0 & inside0 & Hh0 & Hcall0).
    assert (forall k b ins fld y, history k = Event_Write b ins yo fld y ->
      (forall xs, ~ names N y (vdata c_set [VList xs])) \/
      (m0 < k /\ ((forall k' b' ins' fld' y', k' < k -> history k' = Event_Write b' ins' yo fld' y' ->
         SetInv y' k') -> SetInv y k))) as Hstep.
    { intros k b ins fld y Hwrite.
      assert (b = owner h0) as ->.
      { apply (Hkeeps h0 (owner h0) from0 yo b k).
        split; [split; [split; [exists inside0; exact Hcall0 | exact I] | exists m0; eauto] |].
        unfold touches. eauto 7. }
      destruct (Hwriters h0 from0 yo (owner h0) ins k)
        as (f & x & kf & [(from' & a & [[Ha Hcalled'] Hmakes']) Hacc] & Hwhere).
      { split; [split; [exact Hcalled0 | exists m0, cls0, hs0; exact Hmake0] | exists fld, y; exact Hwrite]. }
      pose proof (Hwalk h0 from' Hcalled' a (makes_direct Hmakes') f Hmakes' x (owner h0) kf Ha Hacc) as Hof.
      destruct Hwhere as [-> | (g & t & j & -> & Happ)].
      - left. exact (proj1 (Hof k ltac:(rewrite Hwrite; cbn; auto)) _ _ _ _ Hwrite).
      - right. destruct (proj2 (Hof j (makes_direct Happ)) g t Happ) as [_ Hin].
        destruct (proj1 (Hin k ltac:(rewrite Hwrite; cbn; auto)) _ _ _ _ Hwrite)
          as [(mk & bm & insm & clsm & hsm & Hmk & Hmade') Hset].
        pose proof (made_at_one C Hmade' Hmake0) as ->. split; [exact Hmk | exact Hset]. }
    assert (forall (n : nat) k b ins fld y, k < m0 + Z.of_nat n -> history k = Event_Write b ins yo fld y ->
      SetInv y k) as Hn.
    { induction n as [| n IHn]; intros k b ins fld y Hk Hwrite;
        destruct (Hstep k b ins fld y Hwrite) as [Hno | [Hlate Hset]].
      - intros xs Hxs. destruct (Hno xs Hxs).
      - lia.
      - intros xs Hxs. destruct (Hno xs Hxs).
      - apply Hset. intros k' b' ins' fld' y' Hk' Hw'. apply (IHn k' b' ins' fld' y'); [lia | exact Hw']. }
    intros k b ins fld y Hwrite. apply (Hn (Z.to_nat (k - m0 + 1)) k b ins fld y); [lia | exact Hwrite]. }
  (* and the function, once it has returned, has found the thread among them or interrupted it *)
  intros h f x c k g t a r b [[[(from' & a0 & [[Ha0 Hcalled'] Hmakes']) Hacc] Happ] Hdone].
  destruct (proj2 (Hwalk h from' Hcalled' a0 (makes_direct Hmakes') f Hmakes' x c k Ha0 Hacc a
    (makes_direct Happ)) g t Happ) as [Hinvoke Hin].
  destruct Hdone as [[(insd & spd & Hat) _] | [_ [spd Hend]]]; [rewrite Hinvoke in Hat; discriminate Hat |].
  replace b with (b - 1 + 1) by lia.
  apply (proj2 (Hin (b - 1) ltac:(rewrite Hend; cbn; auto)) r spd Hend).
  intros yo k' b' ins' fld' y' _ Hw' Hcell. exact (Hinv yo Hcell k' b' ins' fld' y' Hw').
Qed.

(** What it is from can hold: an execution in which nothing happens meets each. *)
