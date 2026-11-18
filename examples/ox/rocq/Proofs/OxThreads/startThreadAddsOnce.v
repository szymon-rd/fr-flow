Require Export FrFlowGen.OxThreads.startThreadAddsOnce.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.

(** Proven of `ThreadHerd.startThread`'s tree: what it does itself before it adds the thread is two checks, a
    read of the factory, the factory's call and a read of the set, none of which adds; and after it, it starts
    the thread and ends. *)
Lemma startThreadAddsOnce_Proofs_complete : startThreadAddsOnce_Obl_complete.
Proof.
  intros history [N C] Hmade h code c from s t a s2 t2 a2 [[Hcalled Hadds] Hadds2].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  assert (forall w, direct c from (history w) ->
    forall s t, itselfMakes history (Invocation_mk L.KeySetView_add [s; t]) c from w ->
    forall s' t' w', w' < w -> itselfMakes history (Invocation_mk L.KeySetView_add [s'; t']) c from w' -> False) as Hall.
  { refine (method_meets _ C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl _).
    intros args k Hargs _. apply vals_one in Hargs as (vcode & -> & _).
    (* the two checks; the factory is read, and asked for a thread; the set is read *)
    pass_to L.KeySetView_add.
    (* and the thread is added to it; what follows adds nothing *)
    step. intros wa ysa _ Hpast _ Hadd. split; [| intros; pass; pass].
    intros s0 t0 _ s' t' w' Hlt Hearlier.
    pose proof (Hpast w' ltac:(lia) (makes_direct Hearlier)) as Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]); try contradiction; revert Hearlier; miss. }
  destruct (Z_lt_le_dec a a2) as [Hlt | Hge].
  { exfalso. exact (Hall a2 (makes_direct Hadds2) s2 t2 Hadds2 s t a Hlt Hadds). }
  destruct (Z.eq_dec a a2) as [E | Hne]; [exact E | exfalso].
  exact (Hall a (makes_direct Hadds) s t Hadds s2 t2 a2 ltac:(lia) Hadds2).
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
