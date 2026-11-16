Require Export FrFlowGen.OxThreads.aHerdsFlagIsNew.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of what making a herd runs: the call of the constructor makes the object, calls
    `new AtomicBoolean(false)`, and writes what that returned to the herd's flag; what a val is given, it holds. *)
Lemma aHerdsFlagIsNew_Proofs_complete : aHerdsFlagIsNew_Obl_complete.
Proof.
  intros heldIn history [N C] Hgiven f c h from to Hdone.
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hbegun] [sp Hend]]].
  { destruct (constructor_not_atomic C "ox.internal.ThreadHerd"
      "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hat ltac:(vm_compute; reflexivity) eq_refl). }
  assert (forall k, direct c from (history k) ->
    forall sp, history k = Event_Respond c from (Response_Returned h) sp ->
    exists a b, ((from < a /\ b <= k + 1) /\ itselfMakes history (Invocation_mk
      "java.util.concurrent.atomic.AtomicBoolean <init> scala.Boolean:java.util.concurrent.atomic.AtomicBoolean"
      [Value_Bool_ False]) c from a) /\ completedBy history (Invocation_mk
      "java.util.concurrent.atomic.AtomicBoolean <init> scala.Boolean:java.util.concurrent.atomic.AtomicBoolean"
      [Value_Bool_ False]) c a (Response_Returned (heldIn "ox.internal.ThreadHerd shutdownInProgress" h)) b) as Hall.
  { refine (constructor_meets _ C "ox.internal.ThreadHerd"
      "java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd" Hbegun ltac:(vm_compute; reflexivity) eq_refl _).
    intros args k Hargs Hpassed.
    inversion Hpassed as [| pf vfactory psf vsf Hfactory Hrest]; subst. inversion Hrest; subst. typed Hfactory.
    (* the object is made; its factory and its owner are written *)
    step. intros wmade xmade Hwmade _ Hop. typed_all. split; [miss |].
    pass. pass. pass. pass. pass.
    (* `new AtomicBoolean(false)` is called, and what it returns written to the flag *)
    step. intros wnew ysnew Hwnew _ Hysnew Hmknew. apply args_one in Hysnew as (yfalse & -> & Hyfalse).
    split; [miss |]. intros wgot rnew xnew Hwgot Hdonenew Hgivesnew _.
    pass.
    step. intros wset xset Hwset _ Hopset. typed_all. split; [miss |].
    (* the set is made and written; the call returns the object *)
    pass. pass. pass.
    meets_head. apply meets_ret. intros rr Hk _ Hrr Hgives sp' Hresp.
    rewrite Hrr in Hresp. injection Hresp as -> _.
    apply named_bool in Hyfalse. cbn in Hyfalse. subst yfalse.
    destruct rnew as [ynew | ynew]; [| contradiction].
    match goal with
    | Hcls : class_at N ?r = "ox.internal.ThreadHerd", Eset : history wset = Event_Write _ _ ?yo _ ?yw,
      Hyo : at_place N ?yo ?r, Hyw : names N ?yw _ |- _ =>
        unfold at_place in Hyo; rewrite Hcls in Hyo, Eset; pose proof (one_name N _ _ _ Hyo Hgives) as Eo;
        pose proof (one_name N _ _ _ Hyw Hgivesnew) as Ew; rewrite Eo, Ew in Eset;
        apply (proj2 (proj1 (Hgiven h))) in Eset; subst ynew
    end.
    exists wnew, wgot. split; [split; [lia | exact (done_made Hdonenew)] | exact (done_completed Hdonenew)]. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as (a & b & [[Ha Hb] Hit] & Hd).
  exists a, b. split; [split; [split; [exact Ha | lia] | exact Hit] | exact Hd].
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma aHerdsFlagIsNew_Proofs_feasible : aHerdsFlagIsNew_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h. repeat split; intros w by_ inside written H; discriminate H.
Qed.
