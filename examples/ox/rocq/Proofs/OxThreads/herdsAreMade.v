Require Export FrFlowGen.OxThreads.herdsAreMade.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.
Require FrFlow.Scala.Jdk.

(** Proven of the two things that make a herd. A call of the constructor first makes the object, and what it
    returns at the end is that object. The scope's `apply` makes a herd in place, and the scope it returns holds
    that herd. *)
Lemma herdsAreMade_Proofs_complete : herdsAreMade_Obl_complete.
Proof.
  intros history heldIn [N C] Hscopeholds Hconstructed h w Hcalled.
  destruct (Hconstructed h w Hcalled) as [(taking & c & from & to & Hto & Hdone) |
    (supervisor & errorMode & parent & locals & s & from & to & [[Hto [c Hdone]] <-])].
  - destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hbegun] [sp Hend]]].
    { destruct (constructor_not_atomic C "ox.internal.ThreadHerd"
        "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hat ltac:(vm_compute; reflexivity) eq_refl). }
    assert (forall k, direct c from (history k) -> forall sp, history k = Event_Respond c from (Response_Returned h) sp ->
      exists m b ins hs, m < k /\ history m = Event_Make b ins h "ox.internal.ThreadHerd" hs) as Hall.
    { refine (constructor_meets _ C "ox.internal.ThreadHerd"
        "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hbegun ltac:(vm_compute; reflexivity) eq_refl _).
      intros args k Hargs Hpassed.
      inversion Hpassed as [| pf vfactory psf vsf Hfactory Hrest]; subst. inversion Hrest; subst. typed Hfactory.
      (* the object is made *)
      step. intros wmade xmade Hwmade _ Hop. typed_all. split; [miss |].
      (* its fields are given what the initialisers give; a call among them may throw *)
      repeat pass.
      (* and it is what the call returns *)
      meets_head. apply meets_ret. intros rr Hk _ Hrr Hgives sp' Hresp.
      rewrite Hrr in Hresp. injection Hresp as -> _.
      match goal with Emade : history wmade = Event_Make _ _ ?y _ ?hs, Hy : names N ?y _ |- _ =>
        rewrite (one_name N _ _ _ Hy Hgives) in Emade; exists wmade, c, (Some from), hs; split; [lia | exact Emade] end. }
    destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as (m & b & ins & hs & Hm & Hmade).
    exists m, b, ins, hs. split; [lia | exact Hmade].
  - destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
    { exfalso. exact (module_not_atomic C "ox.OxError$" "apply"
        "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hat ltac:(vm_compute; reflexivity)
        eq_refl ltac:(vm_compute; reflexivity)). }
    assert (forall k, direct c from (history k) ->
      forall sp, history k = Event_Respond c from (Response_Returned s) sp ->
      exists m b ins hs, m < k /\
        history m = Event_Make b ins (heldIn "ox.OxError herd" s) "ox.internal.ThreadHerd" hs) as Hall.
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
      all: apply meets_ret; intros rr Hk _ Hrr Hgives sp' Hresp; rewrite Hrr in Hresp; injection Hresp as -> _.
      all: try (destruct Hgives; fail).
      destruct rmk as [ymk | ymk]; [| contradiction]. pose proof (one_name N _ _ _ Hgivesmk Hgives) as ->.
      rewrite (Hscopeholds yherd yb yc yd ye yf s wmk (Response_Returned s) (wmkd + 1)); [| | reflexivity].
      2: { exists c. right. split; [exists (Some from); exact Hinvmk |]. exists spmk.
           replace (wmkd + 1 - 1) with wmkd by lia. exact Hrespmk. }
      exists wherd, c, (Some from), hsherd. split; [lia | exact Heherd]. }
    destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as (m & b & ins & hs & Hm & Hmade).
    exists m, b, ins, hs. split; [lia | exact Hmade].
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma herdsAreMade_Proofs_feasible : herdsAreMade_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter), (fun _ x => x).
  split; [exact rest_runs |].
  split.
  { intros h finalizers supervisor errorMode parent locals s from response to [who H].
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
