Require Export FrFlowGen.OxThreads.herdsAreMade.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of what making a herd runs: the call of the constructor first makes the object, and what it returns
    at the end is that object. *)
Lemma herdsAreMade_Proofs_complete : herdsAreMade_Obl_complete.
Proof.
  intros history [N C] Hconstructed h w Hcalled.
  destruct (Hconstructed h w Hcalled) as (taking & c & from & to & Hto & Hdone).
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hbegun] [sp Hend]]].
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
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma herdsAreMade_Proofs_feasible : herdsAreMade_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
