Require Export FrFlowGen.OxThreads.unsupervisedComesToItsScope.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.

(** Proven of `unsupervised`'s tree, gone through in time. Given its turn, the call reads the thread's scope,
    which is responded to; it makes a scope with it as parent, which returns a scope in time; and it calls
    `scopedWithCapability` with the scope made and a function it writes. *)
Lemma unsupervisedComesToItsScope_Proofs_complete : unsupervisedComesToItsScope_Obl_complete.
Proof.
  intros history [N C] Hmaking Hproceeds Hscoperesp Hscope locals code c from Hcalled.
  destruct Hcalled as [[inside Hcall] | (a0 & ins & sp & Hat)].
  2: { exfalso. exact (module_not_atomic C "ox.unsupervised$package$" "unsupervised"
      "1,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hat ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)). }
  pose proof (proceeds_moves _ _ _ (Hproceeds locals code c from (or_introl (ex_intro _ inside Hcall)))) as Hmoves.
  refine (module_leads _ C "ox.unsupervised$package$" "unsupervised"
    "1,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl eq_refl
    ltac:(vm_compute; reflexivity) Hmoves _).
  intros args Hargs Hpassed.
  inversion Hargs as [| ? vlocals ? rest Hvlocals Hrest]; subst.
  apply vals_one in Hrest as (vcode & -> & Hvcode).
  inversion Hpassed as [| p1 v1 ps1 vs1 Hlocals Hpassed1]; subst.
  inversion Hpassed1 as [| p2 v2 ps2 vs2 Hcode _]; subst. typed Hlocals. typed Hcode.
  (* the thread's scope is read: that is responded to, and returns *)
  lstep. intros wget ysget Hwget Hqget Hysget Hmkget. apply args_none in Hysget as ->.
  split.
  { intros Hinv. destruct (proj1 (Hscoperesp locals) c wget (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wgetd rget xget Hwgetd Hqgetd Hdoneget Hgivesget Hretget.
  destruct (proj1 (Hscope locals) _ _ _ (done_by_someone Hdoneget)) as (yprevious & ->).
  destruct xget as [e | vprevious]; [contradiction |].
  (* a scope is made: that returns a scope, in time *)
  lstep. intros wapp ysapp Hwapp Hqapp Hysapp Hinvapp. cbn in Hysapp.
  inversion Hysapp as [| ysup ? ysups ? _ Hysups]; subst.
  inversion Hysups as [| yem ? yems ? _ Hyems]; subst. inversion Hyems as [| ypar ? ypars ? _ Hypars]; subst.
  apply args_one in Hypars as (yloc & -> & Hyloc). pose proof (one_name N _ _ _ Hyloc Hvlocals) as ->.
  destruct (Hmaking ysup yem ypar locals c wapp (or_introl (ex_intro _ _ Hinvapp))) as (s & b & Hmade).
  destruct Hmade as [[(ins & sp & Hat) _] | [_ [spmade Hrespmade]]]; [rewrite Hinvapp in Hat; discriminate Hat |].
  split; [left; exists (b - 1), (Response_Returned s), spmade; exact Hrespmade |].
  intros wappd rapp spapp xapp Hwappd Hqappd Hrespapp Hgivesapp Hretapp.
  assert (rapp = Response_Returned s) as ->.
  { pose proof (responded_once C Hrespmade Hrespapp) as Eb. rewrite Eb in Hrespmade.
    rewrite Hrespapp in Hrespmade. injection Hrespmade as -> _. reflexivity. }
  destruct xapp as [e | vs]; [contradiction |].
  (* and running a function in the scope made is called *)
  lstep_done. intros wsc yssc Hwsc Hqsc Hyssc Hinvsc. cbn in Hyssc.
  apply args_two in Hyssc as (ysc & yg & -> & Hysc & Hyg).
  pose proof (one_name N _ _ _ Hysc Hgivesapp) as ->.
  exists ysup, yem, ypar, s, yg, wapp, (wappd + 1), wsc.
  split; [split; [| lia] | left; exact Hinvsc].
  right. split; [exists (Some from); exact Hinvapp |]. exists spapp.
  replace (wappd + 1 - 1) with wappd by lia. exact Hrespapp.
Qed.
