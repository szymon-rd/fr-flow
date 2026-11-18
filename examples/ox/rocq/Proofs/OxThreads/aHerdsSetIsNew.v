Require Export FrFlowGen.OxThreads.aHerdsSetIsNew.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.
Require FrFlow.Scala.Jdk.

(** Proven of the two things that make a herd. A call of the constructor makes the object, calls
    `ConcurrentHashMap.newKeySet()`, and writes what that returned to the herd's threads. The scope's `apply`
    (`OxError(supervisor, errorMode, parent, locals)`) makes a herd in place, the same way, and makes the scope it
    returns of that herd. What a val is given, it holds. *)
Lemma aHerdsSetIsNew_Proofs_complete : aHerdsSetIsNew_Obl_complete.
Proof.
  intros heldIn history [N C] Hscopeholds Hgiven h w
    [(f & c & from & to & _ & Hdone) | (supervisor & errorMode & parent & locals & s & from & to & [[_ [c Hdone]] <-])].
  - destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hbegun] [sp Hend]]].
      { destruct (constructor_not_atomic C "ox.internal.ThreadHerd"
          "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hat ltac:(vm_compute; reflexivity) eq_refl). }
      assert (forall k, direct c from (history k) ->
        forall sp, history k = Event_Respond c from (Response_Returned h) sp ->
        exists a b, ((from < a /\ b <= k + 1) /\ itselfMakes history (Invocation_mk
          L.ConcurrentHashMap_newKeySet
          []) c from a) /\ completedBy history (Invocation_mk
          L.ConcurrentHashMap_newKeySet
          []) c a (Response_Returned (heldIn L.ThreadHerd_threads h)) b) as Hall.
      { refine (constructor_meets _ C "ox.internal.ThreadHerd"
          "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hbegun ltac:(vm_compute; reflexivity) eq_refl _).
        intros args k Hargs Hpassed.
        inversion Hpassed as [| pf vfactory psf vsf Hfactory Hrest]; subst. inversion Hrest; subst. typed Hfactory.
        (* the object is made; its factory, its owner and its flag are written *)
        step. intros wmade xmade Hwmade _ Hop. typed_all. split; [miss |].
        pass_to L.ConcurrentHashMap_newKeySet.
        (* `newKeySet()` is called, and what it returns written to the set; the call returns the object *)
        step. intros wnew ysnew Hwnew _ Hysnew Hmknew. apply args_none in Hysnew as ->.
        split; [miss |]. intros wgot rnew xnew Hwgot Hdonenew Hgivesnew _.
        pass.
        step. intros wset xset Hwset _ Hopset. typed_all. split; [miss |].
        meets_head. apply meets_ret. intros rr Hk _ Hrr Hgives sp' Hresp.
        rewrite Hrr in Hresp. injection Hresp as -> _.
        destruct rnew as [ynew | ynew]; [| contradiction].
        match goal with
        | Hcls : class_at N ?r = "ox.internal.ThreadHerd", Eset : history wset = Event_Write _ _ ?yo _ ?yw,
          Hyo : at_place N ?yo ?r, Hyw : names N ?yw _ |- _ =>
            unfold at_place in Hyo; rewrite Hcls in Hyo, Eset; pose proof (one_name N _ _ _ Hyo Hgives) as Eo;
            pose proof (one_name N _ _ _ Hyw Hgivesnew) as Ew; rewrite Eo, Ew in Eset;
            apply (proj2 (Hgiven h)) in Eset; subst ynew
        end.
        exists wnew, wgot. split; [split; [lia | exact (done_made Hdonenew)] | exact (done_completed Hdonenew)]. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as (a & b & _ & Hd).
    exists a, b, c. exact Hd.
  - destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
    { exfalso. exact (module_not_atomic C "ox.OxError$" "apply"
        "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hat ltac:(vm_compute; reflexivity)
        eq_refl ltac:(vm_compute; reflexivity)). }
    assert (forall k, direct c from (history k) ->
      forall sp, history k = Event_Respond c from (Response_Returned s) sp ->
      exists a b who, completedBy history (Invocation_mk
      L.ConcurrentHashMap_newKeySet
      []) who a
        (Response_Returned (heldIn L.ThreadHerd_threads (heldIn L.OxError_herd s))) b) as Hall.
    { refine (module_meets _ C "ox.OxError$" "apply"
        "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hcall ltac:(vm_compute; reflexivity)
        eq_refl eq_refl ltac:(vm_compute; reflexivity) _).
      intros args k Hargs Hpassed.
      inversion Hargs as [| ? vsupervisor ? rest1 Hvsupervisor Hrest1]; subst.
      inversion Hrest1 as [| ? verrormode ? rest2 Hverrormode Hrest2]; subst.
      inversion Hrest2 as [| ? vparent ? rest3 Hvparent Hrest3]; subst.
      apply vals_one in Hrest3 as (vlocals & -> & Hvlocals).
      inversion Hpassed as [| p1 v1 ps1 vs1 Htsupervisor Hp1]; subst.
      inversion Hp1 as [| p2 v2 ps2 vs2 Hterrormode Hp2]; subst.
      inversion Hp2 as [| p3 v3 ps3 vs3 Htparent Hp3]; subst.
      inversion Hp3 as [| p4 v4 ps4 vs4 Htlocals _]; subst.
      lazy beta iota zeta delta -[identity receiver held names Jdk.as_exn] in Htsupervisor, Hterrormode.
      destruct Htsupervisor as [Htsupervisor _]. destruct Hterrormode as [Hterrormode _]. typed Htlocals.
      assert (held vparent = oret vparent) as Hheldparent.
      { lazy beta iota zeta delta -[identity receiver held names Jdk.as_exn] in Htparent.
        destruct Htparent as [-> | [(x & -> & _) | ->]]; reflexivity. }
      clear Htparent.
      (* the scope's herd is made, in place *)
      step. intros wherd xherd Hwherd _ Hopherd. cbn [op_event] in Hopherd.
      destruct Hopherd as (rherd & yherd & hsherd & -> & Hclassherd & Hyherd & Hholdingherd & Heherd).
      split; [miss |].
      do 8 pass.
      (* `ConcurrentHashMap.newKeySet()` is called, and what it returns written to the herd's threads *)
      step. intros wnew ysnew Hwnew _ Hysnew Hmknew. apply args_none in Hysnew as ->.
      split; [miss |]. intros wgot rnew xnew Hwgot Hdonenew Hgivesnew _.
      pass.
      step. intros wset xset Hwset _ Hopset. cbn [op_event] in Hopset.
      destruct Hopset as (yo & yw & -> & Hyo & Hyw & Heset). split; [miss |].
      do 1 pass.
      (* the scope is made of the herd, and holds it; what is made is what the call returns *)
      meets_head; [pass |].
      step_rule. intros wmk ysmk Hwmk _ Hysmk Hinvmk. cbn in Hysmk.
      inversion Hysmk as [| ya ? yas ? Hya Hyas]; subst. pose proof (one_name N _ _ _ Hya Hyherd) as ->.
      inversion Hyas as [| yb ? ybs ? _ Hybs]; subst. inversion Hybs as [| yc ? ycs ? _ Hycs]; subst.
      inversion Hycs as [| yd ? yds ? _ Hyds]; subst. inversion Hyds as [| ye ? yes ? _ Hyes]; subst.
      apply args_one in Hyes as (yf & -> & _). split; [miss |].
      intros wmkd rmk spmk xmk Hwmkd Hrespmk Hgivesmk.
      meets_head.
      all: apply meets_ret; intros rr Hk _ Hrr Hgives sp' Hresp; rewrite Hrr in Hresp; injection Hresp as -> _.
      all: try (destruct Hgives; fail).
      destruct rmk as [ymk | ymk]; [| contradiction]. pose proof (one_name N _ _ _ Hgivesmk Hgives) as ->.
      rewrite (Hscopeholds yherd yb yc yd ye yf s wmk (Response_Returned s) (wmkd + 1)); [| | reflexivity].
      2: { exists c. right. split; [exists (Some from); exact Hinvmk |]. exists spmk.
           replace (wmkd + 1 - 1) with wmkd by lia. exact Hrespmk. }
      destruct rnew as [ynew | ynew]; [| contradiction].
      unfold at_place in Hyo. rewrite Hclassherd in Hyo, Heset.
      pose proof (one_name N _ _ _ Hyo Hyherd) as ->. pose proof (one_name N _ _ _ Hyw Hgivesnew) as ->.
      apply (proj2 (Hgiven yherd)) in Heset. subst ynew.
      exists wnew, wgot, c. exact (done_completed Hdonenew). }
    exact (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend).
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
