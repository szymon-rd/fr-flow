Require Export FrFlowGen.OxThreads.aReadyHerdsValsAreWritten.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.
Require FrFlow.Scala.Jdk.

(** Proven of the two things that make a herd, each gone through to its end: a call of the constructor, and the
    scope's `apply`, which makes a herd in place. Each makes the herd itself, and writes each field it marks
    before it marks the next; what it returns at the end is the herd, or the scope that holds it. And a herd's
    vals are marked and written only inside the call that makes it. *)
Lemma aReadyHerdsValsAreWritten_Proofs_complete : aReadyHerdsValsAreWritten_Obl_complete.
Proof.
  intros heldIn history [N C] Hassigned Hscopeholds h w Hready field by_ inside later [Hfield Hlater].
  revert by_ inside later Hlater.
  destruct Hready as [(taking & c & from & to & Hto & Hdone) |
    (supervisor & errorMode & parent & locals & s & from & to & [[Hto [c Hdone]] <-])].
  - destruct Hdone as [[(ins & sp & Hat) _] | [[inside0 Hbegun] [sp Hend]]].
    { destruct (constructor_not_atomic C "ox.internal.ThreadHerd"
        "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hat ltac:(vm_compute; reflexivity) eq_refl). }
    assert (forall k, direct c from (history k) ->
      forall sp, history k = Event_Respond c from (Response_Returned h) sp ->
      (exists m hs, history m = Event_Make c (Some from) h "ox.internal.ThreadHerd" hs) /\
      forall m f, m < k -> history m = Event_Mark c (Some from) h f ->
        exists k' v, m < k' /\ k' < k /\ history k' = Event_Write c (Some from) h f v) as Hall.
    { refine (constructor_meets _ C "ox.internal.ThreadHerd"
        "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hbegun ltac:(vm_compute; reflexivity) eq_refl _).
      intros args k Hargs Hpassed.
      inversion Hpassed as [| pf vfactory psf vsf Hfactory Hrest]; subst. inversion Hrest; subst. typed Hfactory.
      (* the object is made *)
      step. intros wherd xherd Hwherd _ Hopherd. cbn [op_event] in Hopherd.
      destruct Hopherd as (rherd & yherd & hsherd & -> & Hclassherd & Hyherd & Hholdingherd & Heherd).
      split; [miss |].
      (* each field is marked and then written what its initialiser gave; a call among them may throw *)
      repeat pass.
      (* and what the call returns is the object *)
      meets_head. apply meets_ret. intros rr Hk Hpast Hrr Hgives sp' Hresp.
      rewrite Hrr in Hresp. injection Hresp as -> _.
      pose proof (one_name N _ _ _ Hyherd Hgives) as ->.
      rename h into yherd.
      unfold at_place in *. rewrite <- Hclassherd in Hyherd.
      repeat match goal with Hp : names N ?yo (vref (class_at N rherd) rherd) |- _ =>
        tryif constr_eq yo yherd then fail else (pose proof (one_name N _ _ _ Hp Hyherd); subst yo; clear Hp) end.
      split; [exists wherd, hsherd; exact Heherd |].
      intros m f Hm HM. pose proof (Hpast m Hm ltac:(rewrite HM; cbn; auto)) as Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]); [.. | destruct Hin].
      all: first [ solve [miss_now] |
        match goal with E : ?hist ?x = Event_Mark _ _ _ _ |- _ =>
          tryif constr_eq E HM then fail else (rewrite E in HM; injection HM as Ef; subst f) end;
        match goal with W : ?hist ?k' = Event_Write _ _ _ _ ?v |- _ =>
          exists k', v; split; [lia | split; [lia | exact W]] end ]. }
    destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as [Hmade Hmarks].
    intros by_ inside later Hlater. assert (to - 1 < later) as Hlt by lia.
    exact (made_then_settled history N h "ox.internal.ThreadHerd" c from (to - 1) _ sp field C Hmade Hend
      (fun x Hx => constructor_over C "ox.internal.ThreadHerd"
        "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hbegun ltac:(vm_compute; reflexivity) eq_refl
        Hend Hx)
      Hmarks (fun b i x Ha => Hassigned h field b i x (conj Hfield Ha)) by_ inside later Hlt).
  - destruct Hdone as [[(ins & sp & Hat) _] | [[inside0 Hcall] [sp Hend]]].
    { exfalso. exact (module_not_atomic C "ox.OxError$" "apply"
        "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hat ltac:(vm_compute; reflexivity)
        eq_refl ltac:(vm_compute; reflexivity)). }
    set (h := heldIn L.OxError_herd s) in *.
    assert (forall k, direct c from (history k) ->
      forall sp, history k = Event_Respond c from (Response_Returned s) sp ->
      (exists m hs, history m = Event_Make c (Some from) h "ox.internal.ThreadHerd" hs) /\
      forall m f, m < k -> history m = Event_Mark c (Some from) h f ->
        exists k' v, m < k' /\ k' < k /\ history k' = Event_Write c (Some from) h f v) as Hall.
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
      (* the scope's herd is made, in place: each field is marked and then written *)
      step. intros wherd xherd Hwherd _ Hopherd. cbn [op_event] in Hopherd.
      destruct Hopherd as (rherd & yherd & hsherd & -> & Hclassherd & Hyherd & Hholdingherd & Heherd).
      split; [miss |].
      do 12 pass.
      (* the scope is made of the herd, and holds it; what is made is what the call returns *)
      meets_head; [pass |].
      step_rule. intros wmk ysmk Hwmk _ Hysmk Hinvmk. cbn in Hysmk.
      inversion Hysmk as [| ya ? yas ? Hya Hyas]; subst. pose proof (one_name N _ _ _ Hya Hyherd) as ->.
      inversion Hyas as [| yb ? ybs ? _ Hybs]; subst. inversion Hybs as [| yc ? ycs ? _ Hycs]; subst.
      inversion Hycs as [| yd ? yds ? _ Hyds]; subst. inversion Hyds as [| ye ? yes ? _ Hyes]; subst.
      apply args_one in Hyes as (yf & -> & _). split; [miss |].
      intros wmkd rmk spmk xmk Hwmkd Hrespmk Hgivesmk.
      meets_head.
      all: apply meets_ret; intros rr Hk Hpast Hrr Hgives sp' Hresp; rewrite Hrr in Hresp; injection Hresp as -> _.
      all: try (destruct Hgives; fail).
      destruct rmk as [ymk | ymk]; [| contradiction]. pose proof (one_name N _ _ _ Hgivesmk Hgives) as ->.
      assert (h = yherd) as ->.
      { apply (Hscopeholds yherd yb yc yd ye yf s wmk (Response_Returned s) (wmkd + 1)); [| reflexivity].
        exists c. right. split; [exists (Some from); exact Hinvmk |]. exists spmk.
        replace (wmkd + 1 - 1) with wmkd by lia. exact Hrespmk. }
      unfold at_place in *. rewrite <- Hclassherd in Hyherd.
      repeat match goal with Hp : names N ?yo (vref (class_at N rherd) rherd) |- _ =>
        tryif constr_eq yo yherd then fail else (pose proof (one_name N _ _ _ Hp Hyherd); subst yo; clear Hp) end.
      split; [exists wherd, hsherd; exact Heherd |].
      intros m f Hm HM. pose proof (Hpast m Hm ltac:(rewrite HM; cbn; auto)) as Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]); [.. | destruct Hin].
      all: first [ solve [miss_now] |
        match goal with E : ?hist ?x = Event_Mark _ _ _ _ |- _ =>
          tryif constr_eq E HM then fail else (rewrite E in HM; injection HM as Ef; subst f) end;
        match goal with W : ?hist ?k' = Event_Write _ _ _ _ ?v |- _ =>
          exists k', v; split; [lia | split; [lia | exact W]] end ]. }
    destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as [Hmade Hmarks].
    intros by_ inside later Hlater. assert (to - 1 < later) as Hlt by lia.
    exact (made_then_settled history N h "ox.internal.ThreadHerd" c from (to - 1) _ sp field C Hmade Hend
      (fun x Hx => module_over C "ox.OxError$" "apply"
        "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hcall ltac:(vm_compute; reflexivity)
        eq_refl eq_refl ltac:(vm_compute; reflexivity) Hend Hx)
      Hmarks (fun b i x Ha => Hassigned h field b i x (conj Hfield Ha)) by_ inside later Hlt).
Qed.
