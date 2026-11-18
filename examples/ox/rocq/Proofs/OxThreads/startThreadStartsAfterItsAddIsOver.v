Require Export FrFlowGen.OxThreads.startThreadStartsAfterItsAddIsOver.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.startThread`'s tree: it adds the thread to the set, goes on once that call is responded
    to, and only then starts the thread; and the add is the one call it makes that adds. *)
Lemma startThreadStartsAfterItsAddIsOver_Proofs_complete : startThreadStartsAfterItsAddIsOver_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h code c t from w m started [[Hcalled Hadds] Hstarts] [Hwm [Hbegun Hnotover]].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  apply Hnotover.
  refine (method_meets
    (fun m => forall started,
      itselfMakes history (Invocation_mk L.Thread_start [started]) c from m ->
      forall s t w, itselfMakes history (Invocation_mk
        L.KeySetView_add [s; t]) c from w ->
        w < m -> begun history (Invocation_mk
          L.KeySetView_add [s; t]) c w ->
        overBy history c w m)
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl _ m
    (makes_direct Hstarts) started Hstarts _ t w Hadds Hwm Hbegun).
  intros args k Hargs _. apply vals_one in Hargs as (vcode & -> & _).
  (* the two checks; the factory is read, and asked for a thread; the set is read *)
  pass_to L.KeySetView_add.
  (* the thread is added to it: no start; the call goes on once the add is responded to *)
  step. intros wa ysa _ _ _ Hadd. split.
  { intros started' Hst. pose proof (makes_one Hadd Hst) as E. discriminate E. }
  intros wadded radd xadd Hwadded Hdone _ _. meets_head; [pass |].
  (* then it starts the thread: an add made before is the one, and is over *)
  step_rule. intros wstart yst Hle Hpast _ Hmk. split; [| intros; pass].
  intros started' Hst s t' wa' Hadd' Hlt Hbegun'.
  pose proof (Hpast wa' Hlt (makes_direct Hadd')) as Hin. cbn [In] in Hin.
  destruct Hin as [<- | Hin].
  { destruct Hdone as [(sp & Hat & _) | (Hinv & _ & sp & Hresp)].
    - destruct Hbegun' as [ins E]. rewrite Hat in E. discriminate E.
    - exists (wadded - 1), radd, sp. split; [lia | exact Hresp]. }
  repeat (destruct Hin as [<- | Hin]); try contradiction; revert Hadd'; miss.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
