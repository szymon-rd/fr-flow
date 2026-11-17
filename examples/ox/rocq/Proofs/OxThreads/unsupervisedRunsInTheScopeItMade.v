Require Export FrFlowGen.OxThreads.unsupervisedRunsInTheScopeItMade.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `unsupervised`'s tree, gone through whole: it reads the thread's scope, makes a scope with it as
    parent, and calls `scopedWithCapability` with the scope made; what that gives, it gives. The call that made
    the scope is one of these, and no other makes a scope: so the scope it ran the code in is the one made. *)
Lemma unsupervisedRunsInTheScopeItMade_Proofs_complete : unsupervisedRunsInTheScopeItMade_Obl_complete.
Proof.
  intros history [N C] c s from to (supervisor & errorMode & parent & locals & code & ended & a & b &
    [[Hdone Hmakes] Hmade]).
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (module_not_atomic C "ox.unsupervised$package$" "unsupervised"
      "1,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hat ltac:(vm_compute; reflexivity) eq_refl
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
      - exact (module_over C "ox.unsupervised$package$" "unsupervised"
          "1,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl eq_refl
          ltac:(vm_compute; reflexivity) Hrr Hlater (makes_direct Hmakes)). }
    refine (module_meets _ C "ox.unsupervised$package$" "unsupervised"
      "1,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl eq_refl
      ltac:(vm_compute; reflexivity) _).
    intros args k Hargs Hpassed.
    inversion Hargs as [| ? vlocals ? rest Hvlocals Hrest]; subst.
    apply vals_one in Hrest as (vcode & -> & Hvcode).
    inversion Hpassed as [| p1 v1 ps1 vs1 Hlocals Hpassed1]; subst.
    inversion Hpassed1 as [| p2 v2 ps2 vs2 Hcode _]; subst. typed Hlocals. typed Hcode.
    (* the thread's scope is read *)
    step. intros wget ysget Hwget _ Hysget Hmkget. split; [miss |].
    intros wgetd rget xget Hwgetd Hdoneget Hgivesget Hretget.
    meets_head.
    { apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp. exfalso.
      pose proof (Hamong _ _ _ Hrr Hpast) as Hin. cbn [In] in Hin. destruct Hin as [<- | []].
      destruct Hmakes as [E | (? & ? & E)]; destruct Hmkget as [E' | (? & ? & E')]; rewrite E in E';
        discriminate E'. }
    (* a scope is made *)
    step_rule. intros wapp ysapp Hwapp _ Hysapp Hinvapp. split; [miss |].
    intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp.
    destruct xapp as [e | vs].
    { (* making the scope threw: so does this call, and no scope was made *)
      meets_head. apply meets_ret. intros rr Hk Hpast Hrr Hgives ended' sp' Hresp. exfalso.
      pose proof (Hamong _ _ _ Hrr Hpast) as Hin. cbn [In] in Hin. destruct Hin as [<- | [<- | []]].
      - destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |].
        pose proof (responded_once C Hrespm Hrespapp) as Eb. rewrite Eb in Hrespm. rewrite Hrespapp in Hrespm.
        injection Hrespm as -> _. exact Hgivesapp.
      - destruct Hmakes as [E | (? & ? & E)]; destruct Hmkget as [E' | (? & ? & E')]; rewrite E in E';
          discriminate E'. }
    (* the code is run in the scope made *)
    step. intros wsc yssc Hwsc _ Hyssc Hinvsc. cbn in Hyssc.
    apply args_two in Hyssc as (ysc & yg & -> & Hysc & Hyg). split; [miss |].
    intros wscd rsc spsc xsc Hwscd Hrespsc Hgivessc.
    meets_head.
    all: apply meets_ret; intros rr Hk Hpast Hrr Hgives ended' sp' Hresp.
    all: pose proof (Hamong _ _ _ Hrr Hpast) as Hin; cbn [In] in Hin; destruct Hin as [<- | [<- | [<- | []]]].
    all: try (exfalso; destruct Hmakes as [E | (? & ? & E)]; rewrite Hinvsc in E; discriminate E).
    all: try (exfalso; destruct Hmakes as [E | (? & ? & E)]; destruct Hmkget as [E' | (? & ? & E')];
      rewrite E in E'; discriminate E').
    all: destruct Hmade as [[(? & ? & Hatm) _] | [_ [spm Hrespm]]]; [rewrite Hinvapp in Hatm; discriminate Hatm |].
    all: pose proof (responded_once C Hrespm Hrespapp) as Eb; rewrite Eb in Hrespm; rewrite Hrespapp in Hrespm;
      injection Hrespm as -> _; pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->.
    all: exists yg, wsc, rsc, (wscd + 1); (split; [split; [left; exact Hinvsc | right; split;
      [exists (Some from); exact Hinvsc | exists spsc; replace (wscd + 1 - 1) with wscd by lia; exact Hrespsc]] |
      lia]). }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) ended sp Hend) as (g & a2 & ran & b2 & Hran & Hb2).
  exists g, a2, ran, b2. split; [exact Hran | lia].
Qed.
