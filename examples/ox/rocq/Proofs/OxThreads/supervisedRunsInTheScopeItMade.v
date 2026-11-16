Require Export FrFlowGen.OxThreads.supervisedRunsInTheScopeItMade.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `unsupervised`'s tree, gone through whole: it reads the thread's scope, makes a scope with it as
    parent, and calls `scopedWithCapability` with the scope made; what that gives, it gives. The call that made
    the scope is one of these, and no other makes a scope: so the scope it ran the code in is the one made. *)
Lemma supervisedRunsInTheScopeItMade_Proofs_complete : supervisedRunsInTheScopeItMade_Obl_complete.
Proof.
  intros history [N C] c s from to (supervisor & errorMode & parent & locals & code & ended & a & b &
    [[Hdone Hmakes] Hmade]).
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (module_not_atomic C "ox.supervised$package$" "supervisedError"
      "3,ox.ErrorMode,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hat ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)). }
  assert (forall k, direct c from (history k) ->
    forall ended sp, history k = Event_Respond c from ended sp ->
    exists g a2 ran b2, (itselfMakes history (Invocation_mk
      "ox.unsupervised$package$ scopedWithCapability 1,ox.Ox,scala.Function1:java.lang.Object" [s; g]) c from a2 /\ completedBy history (Invocation_mk
      "ox.unsupervised$package$ scopedWithCapability 1,ox.Ox,scala.Function1:java.lang.Object" [s; g]) c a2 ran b2) /\ b2 <= k)
    as Hall.
  { (* the call that made the scope is an event of this call, before its response *)
    assert (forall k tr rr, history k = Event_Respond c from rr [] -> past history c from k tr -> In a tr)
      as Hamong.
    { intros k tr rr Hrr Hpast. apply Hpast; [| exact (makes_direct Hmakes)].
      destruct (Z_lt_le_dec a k) as [Hlt | Hge]; [exact Hlt | exfalso].
      assert (a = k \/ k < a) as [-> | Hlater] by lia.
      - destruct Hmakes as [E | (? & ? & E)]; rewrite Hrr in E; discriminate E.
      - exact (module_over C "ox.supervised$package$" "supervisedError"
          "3,ox.ErrorMode,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl
          ltac:(vm_compute; reflexivity) Hrr Hlater (makes_direct Hmakes)). }
    refine (module_meets _ C "ox.supervised$package$" "supervisedError"
      "3,ox.ErrorMode,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity) _).
    intros args k Hargs Hpassed.
    inversion Hargs as [| ? vmode ? rest0 Hvmode Hrest0]; subst.
    inversion Hrest0 as [| ? vlocals ? rest Hvlocals Hrest]; subst.
    apply vals_one in Hrest as (vcode & -> & Hvcode).
    inversion Hpassed as [| p0 v0 ps0 vs0 Hmode Hpassed0]; subst.
    inversion Hpassed0 as [| p1 v1 ps1 vs1 Hlocals Hpassed1]; subst.
    inversion Hpassed1 as [| p2 v2 ps2 vs2 Hcode _]; subst. typed Hmode. typed Hlocals. typed Hcode.
    (* a supervisor is made *)
    step. intros wsup yssup Hwsup _ Hyssup Hmksup. split; [miss |].
    intros wsupd rsup xsup Hwsupd Hdonesup Hgivessup Hretsup.
    assert (a <> wsup) as Hnotsup.
    { intros ->. destruct Hmakes as [E | (? & ? & E)]; destruct Hmksup as [E' | (? & ? & E')]; rewrite E in E';
        discriminate E'. }
    meets_head.
    { apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp. exfalso.
      pose proof (Hamong _ _ _ Hrr Hpast) as Hin. cbn [In] in Hin. destruct Hin as [<- | []].
      exact (Hnotsup eq_refl). }
    (* the thread's scope is read *)
    step. intros wget ysget Hwget _ Hysget Hmkget. split; [miss |].
    intros wgetd rget xget Hwgetd Hdoneget Hgivesget Hretget.
    assert (a <> wget) as Hnotget.
    { intros ->. destruct Hmakes as [E | (? & ? & E)]; destruct Hmkget as [E' | (? & ? & E')]; rewrite E in E';
        discriminate E'. }
    meets_head.
    { apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp. exfalso.
      pose proof (Hamong _ _ _ Hrr Hpast) as Hin. cbn [In] in Hin.
      destruct Hin as [<- | [<- | []]]; [exact (Hnotget eq_refl) | exact (Hnotsup eq_refl)]. }
    (* a scope is made *)
    step_typed. intros wapp ysapp Hwapp _ Hysapp Hinvapp. split; [miss |].
    intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp Hretapp.
    destruct xapp as [e | vs].
    { (* making the scope threw: so does this call, and no scope was made *)
      meets_head. apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp. exfalso.
      pose proof (Hamong _ _ _ Hrr Hpast) as Hin. cbn [In] in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; [| exact (Hnotget eq_refl) | exact (Hnotsup eq_refl)].
      destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |].
      pose proof (responded_once C Hrespm Hrespapp) as Eb. rewrite Eb in Hrespm. rewrite Hrespapp in Hrespm.
      injection Hrespm as -> _. exact Hgivesapp. }
    (* the code is run in the scope made *)
    typed Hretapp.
    step_typed. intros wsc yssc Hwsc _ Hyssc Hinvsc. cbn in Hyssc.
    apply args_two in Hyssc as (ysc & yg & -> & Hysc & Hyg). split; [miss |].
    intros wscd rsc spsc xsc Hwscd Hrespsc Hgivessc Hretsc.
    assert (a <> wsc) as Hnotsc.
    { intros ->. destruct Hmakes as [E | (? & ? & E)]; rewrite Hinvsc in E; discriminate E. }
    destruct xsc as [e | vres].
    - (* running the code threw: the handler tells the supervisor, and throws it again *)
      destruct e.
      all: step; intros wadd1 ysadd1 Hwadd1 _ Hysadd1 Hmkadd1; (split; [miss |]).
      all: intros waddd1 radd1 xadd1 Hwaddd1 Hdoneadd1 Hgivesadd1 Hretadd1.
      all: assert (a <> wadd1) as Hnotwadd1 by (intros ->; destruct Hmakes as [E | (? & ? & E)];
        destruct Hmkadd1 as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
      all: meets_head.
      all: try (apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
        pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
        repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
        destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
        pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
        injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
        exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
          [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
            exact Hrespsc]] | lia])).
      all: step; intros wdis1 ysdis1 Hwdis1 _ Hysdis1 Hmkdis1; (split; [miss |]).
      all: intros wdisd1 rdis1 xdis1 Hwdisd1 Hdonedis1 Hgivesdis1 Hretdis1.
      all: assert (a <> wdis1) as Hnotwdis1 by (intros ->; destruct Hmakes as [E | (? & ? & E)];
        destruct Hmkdis1 as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
      all: meets_head.
      all: apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
        pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
        repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
        destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
        pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
        injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
        exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
          [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
            exact Hrespsc]] | lia]).
    - (* running the code gave a result: the error mode is asked whether it is an error *)
      step. intros wis ysis Hwis _ Hysis Hmkis. split; [miss |].
      intros wisd ris xis Hwisd Hdoneis Hgivesis Hretis.
      assert (a <> wis) as Hnotwis by (intros ->; destruct Hmakes as [E | (? & ? & E)];
        destruct Hmkis as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
      destruct xis as [e | vis].
      + (* asking threw: the handler *)
        destruct e.
        all: step; intros wadd2 ysadd2 Hwadd2 _ Hysadd2 Hmkadd2; (split; [miss |]).
        all: intros waddd2 radd2 xadd2 Hwaddd2 Hdoneadd2 Hgivesadd2 Hretadd2.
        all: assert (a <> wadd2) as Hnotwadd2 by (intros ->; destruct Hmakes as [E | (? & ? & E)];
          destruct Hmkadd2 as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
        all: meets_head.
        all: try (apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
          pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
          repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
          destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
          pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
          injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
          exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
            [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
              exact Hrespsc]] | lia])).
        all: step; intros wdis2 ysdis2 Hwdis2 _ Hysdis2 Hmkdis2; (split; [miss |]).
        all: intros wdisd2 rdis2 xdis2 Hwdisd2 Hdonedis2 Hgivesdis2 Hretdis2.
        all: assert (a <> wdis2) as Hnotwdis2 by (intros ->; destruct Hmakes as [E | (? & ? & E)];
          destruct Hmkdis2 as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
        all: meets_head.
        all: apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
          pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
          repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
          destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
          pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
          injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
          exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
            [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
              exact Hrespsc]] | lia]).
      + meets_head.
        * (* an error: the supervisor adds to it what else was thrown *)
          step. intros wsu yssu Hwsu _ Hyssu Hmksu. split; [miss |].
          intros wsud rsu xsu Hwsud Hdonesu Hgivessu Hretsu.
          assert (a <> wsu) as Hnotwsu by (intros ->; destruct Hmakes as [E | (? & ? & E)];
            destruct Hmksu as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
          destruct xsu as [e | vsu].
          { destruct e.
            all: step; intros wadd3 ysadd3 Hwadd3 _ Hysadd3 Hmkadd3; (split; [miss |]).
            all: intros waddd3 radd3 xadd3 Hwaddd3 Hdoneadd3 Hgivesadd3 Hretadd3.
            all: assert (a <> wadd3) as Hnotwadd3 by (intros ->; destruct Hmakes as [E | (? & ? & E)];
              destruct Hmkadd3 as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
            all: meets_head.
            all: try (apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
              pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
              repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
              destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
              pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
              injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
              exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
                [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
                  exact Hrespsc]] | lia])).
            all: step; intros wdis3 ysdis3 Hwdis3 _ Hysdis3 Hmkdis3; (split; [miss |]).
            all: intros wdisd3 rdis3 xdis3 Hwdisd3 Hdonedis3 Hgivesdis3 Hretdis3.
            all: assert (a <> wdis3) as Hnotwdis3 by (intros ->; destruct Hmakes as [E | (? & ? & E)];
              destruct Hmkdis3 as [E' | (? & ? & E')]; rewrite E in E'; discriminate E').
            all: meets_head.
            all: apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
              pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
              repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
              destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
              pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
              injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
              exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
                [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
                  exact Hrespsc]] | lia]).
          }
          meets_head. apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
            pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
            repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
            destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
            pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
            injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
            exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
              [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
                exact Hrespsc]] | lia]).
        * apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp;
            pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin;
            repeat destruct Hin as [Hin | Hin]; try contradiction; try (exfalso; congruence); subst a;
            destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |];
            pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
            injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->;
            exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
              [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia;
                exact Hrespsc]] | lia]).
  }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) ended sp Hend) as (g & a2 & ran & b2 & Hran & Hb2).
  exists g, a2, ran, b2. split; [exact Hran | lia].
Qed.
