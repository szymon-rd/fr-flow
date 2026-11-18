Require Export FrFlowGen.OxThreads.aScopesHerdIsItsMakers.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of the tree of the scope's `apply` (`OxError(supervisor, errorMode, parent, locals)`), gone through
    whole. It makes the herd in place: the herd's constructor asks for the current thread, which is the caller,
    and writes it as the herd's owner. Then it makes the scope of that herd, and returns it. *)
Lemma aScopesHerdIsItsMakers_Proofs_complete : aScopesHerdIsItsMakers_Obl_complete.
Proof.
  intros heldIn history [N C] Hscopeholds Hherdholds Hcurrent supervisor errorMode parent locals c s from to
    Hdone.
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (module_not_atomic C "ox.OxError$" "apply"
      "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hat ltac:(vm_compute; reflexivity)
      eq_refl ltac:(vm_compute; reflexivity)). }
  assert (forall k, direct c from (history k) ->
    forall sp, history k = Event_Respond c from (Response_Returned s) sp ->
    heldIn L.ThreadHerd_herdOwner (heldIn L.OxError_herd s) = c) as Hall.
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
    (* the supervisor and the error mode may be Scala objects: what is kept of each is that a name holds it *)
    lazy beta iota zeta delta -[identity receiver held names Jdk.as_exn] in Htsupervisor, Hterrormode.
    destruct Htsupervisor as [Htsupervisor _]. destruct Hterrormode as [Hterrormode _]. typed Htlocals.
    assert (held vparent = oret vparent) as Hheldparent.
    { lazy beta iota zeta delta -[identity receiver held names Jdk.as_exn] in Htparent.
      destruct Htparent as [-> | [(x & -> & _) | ->]]; reflexivity. }
    clear Htparent.
    (* the scope's herd is made, in place; its factory is written *)
    step. intros wherd xherd Hwherd _ Hopherd. cbn [op_event] in Hopherd.
    destruct Hopherd as (rherd & yherd & hsherd & -> & Hclassherd & Hyherd & Hholdingherd & Heherd).
    split; [miss |].
    pass_to L.Thread_currentThread.
    (* the current thread is asked for: the caller *)
    step. intros wcur yscur Hwcur _ Hyscur Hmkcur. apply args_none in Hyscur as ->. split; [miss |].
    intros wcurd rcur xcur Hwcurd Hdonecur Hgivescur Hretcur.
    rewrite (Hcurrent _ _ _ _ (done_completed Hdonecur)) in Hgivescur.
    destruct xcur as [e | vcur]; [contradiction |].
    pass.
    (* and written as the herd's owner *)
    step. intros wown xown Hwown _ Hopown. cbn [op_event] in Hopown.
    destruct Hopown as (yo & yw & -> & Hyo & Hyw & Heown). split; [miss |].
    assert (unit -> heldIn L.ThreadHerd_herdOwner yherd = c) as Howner.
    { intros _. unfold at_place in Hyo. rewrite Hclassherd in Hyo, Heown.
      pose proof (one_name N _ _ _ Hyo Hyherd) as ->. pose proof (one_name N _ _ _ Hyw Hgivescur) as ->.
      symmetry. exact (proj2 (proj1 (proj1 (Hherdholds yherd))) _ _ _ _ Heown). }
    (* its flag and its set are made; then what the scope keeps its finalizers in *)
    pass. pass. pass. pass. pass. pass. pass.
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
    rewrite (Hscopeholds yherd yb yc yd ye yf s wmk (Response_Returned s) (wmkd + 1)); [exact (Howner tt) | | reflexivity].
    exists c. right. split; [exists (Some from); exact Hinvmk |]. exists spmk.
    replace (wmkd + 1 - 1) with wmkd by lia. exact Hrespmk. }
  exact (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
