Require Export FrFlowGen.OxThreads.aConstructedScopeIsMade.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of what making a scope runs: the call of the constructor first makes the object, and what it returns
    at the end is that object. *)
Lemma aConstructedScopeIsMade_Proofs_complete : aConstructedScopeIsMade_Obl_complete.
Proof.
  intros history [N C] s w (x & x1 & x2 & x3 & x4 & x5 & c & from & to & Hto & Hdone).
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hbegun] [sp Hend]]].
  { destruct (constructor_not_atomic C "ox.OxError"
      "2,ox.internal.ThreadHerd,java.util.concurrent.atomic.AtomicReference,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError"
      Hat ltac:(vm_compute; reflexivity) eq_refl). }
  assert (forall k, direct c from (history k) -> forall sp, history k = Event_Respond c from (Response_Returned s) sp ->
    exists m b ins hs, m < k /\ history m = Event_Make b ins s "ox.OxError" hs) as Hall.
  { refine (constructor_meets _ C "ox.OxError"
      "2,ox.internal.ThreadHerd,java.util.concurrent.atomic.AtomicReference,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError"
      Hbegun ltac:(vm_compute; reflexivity) eq_refl _).
    intros args k Hargs Hpassed.
    repeat (match goal with H : Forall2 _ _ _ |- _ => inversion H; subst; clear H end).
    (* the object is made *)
    step. intros wmade xmade Hwmade _ Hop. typed_all. split; [miss |].
    (* its fields are given what the call was given *)
    repeat pass.
    (* and it is what the call returns *)
    meets_head. apply meets_ret. intros rr Hk _ Hrr Hgives sp' Hresp.
    rewrite Hrr in Hresp. injection Hresp as -> _.
    match goal with Emade : history wmade = Event_Make _ _ ?y _ ?hs, Hy : names N ?y _ |- _ =>
      rewrite (one_name N _ _ _ Hy Hgives) in Emade; exists wmade, c, (Some from), hs; split; [lia | exact Emade] end. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as (m & b & ins & hs & Hm & Hmade).
  exists to, m, b, ins, hs. split; [lia | exact Hmade].
Qed.
