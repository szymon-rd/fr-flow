Require Export FrFlowGen.OxThreads.makingAScopeReturnsInTime.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.
Require FrFlow.Scala.Jdk.

(** Proven of the tree of the scope's `apply` (`OxError(supervisor, errorMode, parent, locals)`), gone through
    in time. Given its turn, the call makes a herd in place: it asks for the current thread, and makes a flag
    and a set, each of which returns in time. It makes what keeps the scope's finalizers, and then the scope,
    by the `apply` the compiler wrote, which returns in time; and it returns what that returned. *)
Lemma makingAScopeReturnsInTime_Proofs_complete : makingAScopeReturnsInTime_Obl_complete.
Proof.
  intros history [N C] Hproceeds Hflag Hset Href Hmade6 Hcurresp Hcurrent supervisor errorMode parent locals c
    from Hcalled.
  destruct Hcalled as [[inside Hcall] | (a0 & ins & sp & Hat)].
  2: { exfalso. exact (module_not_atomic C "ox.OxError$" "apply"
      "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hat ltac:(vm_compute; reflexivity)
      eq_refl ltac:(vm_compute; reflexivity)). }
  pose proof (proceeds_moves _ _ _ (Hproceeds supervisor errorMode parent locals c from
    (or_introl (ex_intro _ inside Hcall)))) as Hmoves.
  refine (module_leads _ C "ox.OxError$" "apply"
    "2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError" Hcall ltac:(vm_compute; reflexivity)
    eq_refl eq_refl ltac:(vm_compute; reflexivity) Hmoves _).
  intros args Hargs Hpassed.
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
  (* the scope's herd is made in place, up to where it asks for the current thread *)
  repeat (leads_head; lazymatch goal with
    | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Call _ _ _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Ret _)) => fail
    | |- _ => lstep_rule; intros
    end).
  lstep. intros wcur yscur Hwcur Hqcur Hyscur Hmkcur. apply args_none in Hyscur as ->.
  split.
  { intros Hinv. destruct (Hcurresp c wcur (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wcurd rcur xcur Hwcurd Hqcurd Hdonecur Hgivescur Hretcur.
  rewrite (Hcurrent _ _ _ _ (done_completed Hdonecur)) in Hgivescur.
  destruct xcur as [e | vcur]; [contradiction |].
  (* the thread is written as the herd's owner; a flag is made *)
  repeat (leads_head; lazymatch goal with
    | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Call _ _ _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Ret _)) => fail
    | |- _ => lstep_rule; intros
    end).
  lstep. intros wfl ysfl Hwfl Hqfl Hysfl Hmkfl. cbn in Hysfl. apply args_one in Hysfl as (yfl & -> & Hyfl).
  pose proof (one_name N _ _ _ Hyfl (of_bool N false)) as ->.
  split.
  { intros Hinv. destruct (proj1 (Hflag (false = true)) c wfl (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wfld rfl xfl Hwfld Hqfld Hdonefl Hgivesfl Hretfl.
  destruct (proj2 (Hflag (false = true)) _ _ _ (done_by_someone Hdonefl)) as (yflag & ->).
  destruct xfl as [e | vflag]; [contradiction |].
  (* it is written; a set is made *)
  repeat (leads_head; lazymatch goal with
    | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Call _ _ _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Ret _)) => fail
    | |- _ => lstep_rule; intros
    end).
  lstep. intros wse ysse Hwse Hqse Hysse Hmkse. apply args_none in Hysse as ->.
  split.
  { intros Hinv. destruct (proj1 Hset c wse (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wsed rse xse Hwsed Hqsed Hdonese Hgivesse Hretse.
  destruct (proj2 Hset _ _ _ (done_by_someone Hdonese)) as (yset & ->).
  destruct xse as [e | vset]; [contradiction |].
  (* it is written; what keeps the scope's finalizers is made *)
  repeat (leads_head; lazymatch goal with
    | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Call _ _ _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Ret _)) => fail
    | |- _ => lstep_rule; intros
    end).
  lstep. intros wre ysre Hwre Hqre Hysre Hmkre. cbn in Hysre. apply args_one in Hysre as (yre & -> & Hyre).
  split.
  { intros Hinv. destruct (proj1 (Href yre) c wre (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wred rre xre Hwred Hqred Hdonere Hgivesre Hretre.
  destruct (proj2 (Href yre) _ _ _ (done_by_someone Hdonere)) as (yref & ->).
  destruct xre as [e | vref0]; [contradiction |].
  (* the scope is made of them, by the `apply` the compiler wrote: that returns, in time *)
  repeat (leads_head; lazymatch goal with
    | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Call _ _ _)) => fail
    | |- leads _ _ _ _ _ _ _ _ (Running (Ret _)) => fail
    | |- _ => lstep_rule; intros
    end).
  lstep. intros wmk ysmk Hwmk Hqmk Hysmk Hinvmk. cbn in Hysmk.
  inversion Hysmk as [| ya ? yas ? _ Hyas]; subst.
  inversion Hyas as [| yb ? ybs ? _ Hybs]; subst. inversion Hybs as [| yc ? ycs ? _ Hycs]; subst.
  inversion Hycs as [| yd ? yds ? _ Hyds]; subst. inversion Hyds as [| ye ? yes ? _ Hyes]; subst.
  apply args_one in Hyes as (yf & -> & _).
  split.
  { destruct (proj1 (Hmade6 ya yb yc yd ye yf) c wmk (conj (ex_intro _ _ Hinvmk) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wmkd rmk spmk xmk Hwmkd Hqmkd Hrespmk Hgivesmk Hretmk.
  destruct (proj2 (Hmade6 ya yb yc yd ye yf) wmk rmk (wmkd + 1)) as (ymade & ->).
  { exists c. right. split; [exists (Some from); exact Hinvmk |]. exists spmk.
    replace (wmkd + 1 - 1) with wmkd by lia. exact Hrespmk. }
  destruct xmk as [e | vmade]; [contradiction |].
  (* and what it returned is what the call returns *)
  leads_head. apply leads_ret. intros wr rr Hwr Hqr Hrr Hgives.
  destruct rr as [yr | yr]; [| contradiction].
  exists yr, (wr + 1). right. split; [exists inside; exact Hcall |]. exists [].
  replace (wr + 1 - 1) with wr by lia. exact Hrr.
Qed.
