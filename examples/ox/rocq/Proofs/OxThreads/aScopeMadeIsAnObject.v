Require Export FrFlowGen.OxThreads.aScopeMadeIsAnObject.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.
Require FrFlow.Scala.Jdk.

(** Proven of the tree of the scope's `apply` (`OxError(supervisor, errorMode, parent, locals)`), gone through
    whole. It makes a herd, and what keeps the scope's finalizers; then it makes the scope of them, by the `apply`
    the compiler wrote, and returns what that returned: an object the class's constructor returned, and so an
    object of the class. *)
Lemma aScopeMadeIsAnObject_Proofs_complete : aScopeMadeIsAnObject_Obl_complete.
Proof.
  intros history [N C] Hmade Hconstructed supervisor errorMode parent locals s from to [c Hdone].
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (module_not_atomic C "ox.OxError$" "apply"
      "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hat ltac:(vm_compute; reflexivity)
      eq_refl ltac:(vm_compute; reflexivity)). }
  assert (forall k, direct c from (history k) ->
    forall sp, history k = Event_Respond c from (Response_Returned s) sp -> scopeMade history s) as Hall.
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
    (* the scope's herd is made in place, and what the scope keeps its finalizers in *)
    do 13 pass.
    (* the scope is made of them, by the `apply` the compiler wrote; what that returns is what the call returns *)
    meets_head; [pass |].
    step_rule. intros wmk ysmk Hwmk _ Hysmk Hinvmk. cbn in Hysmk.
    inversion Hysmk as [| ya ? yas ? _ Hyas]; subst.
    inversion Hyas as [| yb ? ybs ? _ Hybs]; subst. inversion Hybs as [| yc ? ycs ? _ Hycs]; subst.
    inversion Hycs as [| yd ? yds ? _ Hyds]; subst. inversion Hyds as [| ye ? yes ? _ Hyes]; subst.
    apply args_one in Hyes as (yf & -> & _). split; [miss |].
    intros wmkd rmk spmk xmk Hwmkd Hrespmk Hgivesmk.
    meets_head.
    all: apply meets_ret; intros rr Hk _ Hrr Hgives sp' Hresp; rewrite Hrr in Hresp; injection Hresp as -> _.
    all: try (destruct Hgives; fail).
    destruct rmk as [ymk | ymk]; [| contradiction]. pose proof (one_name N _ _ _ Hgivesmk Hgives) as ->.
    apply (Hmade s (wmkd + 1)).
    apply (Hconstructed ya yb yc yd ye yf s wmk (Response_Returned s) (wmkd + 1)); [| reflexivity].
    exists c. right. split; [exists (Some from); exact Hinvmk |]. exists spmk.
    replace (wmkd + 1 - 1) with wmkd by lia. exact Hrespmk. }
  exact (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend).
Qed.
