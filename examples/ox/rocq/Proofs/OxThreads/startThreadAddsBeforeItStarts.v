Require Export FrFlowGen.OxThreads.startThreadAddsBeforeItStarts.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.startThread`'s tree: what it does itself before it adds the thread is two checks, a
    read of the factory, the factory's call and a read of the set; none starts a thread. *)
Lemma startThreadAddsBeforeItStarts_Proofs_complete : startThreadAddsBeforeItStarts_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h code c t from w m started [[Hcalled Hadds] Hstarts].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  refine (method_meets
    (fun w => forall s t, itselfMakes history (Invocation_mk
      "java.util.concurrent.ConcurrentHashMap$.KeySetView add java.lang.Object:scala.Boolean" [s; t]) c from w ->
      forall m started,
        itselfMakes history (Invocation_mk "java.lang.Thread start :scala.Unit" [started]) c from m -> w < m)
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl _ w
    (makes_direct Hadds) _ t Hadds m started Hstarts).
  intros args k Hargs _. apply vals_one in Hargs as (vcode & -> & _).
  (* the two checks; the factory is read, and asked for a thread; the set is read *)
  pass. pass. pass. pass. pass.
  (* and the thread is added to it; what follows adds nothing *)
  step. intros wa ysa _ Hpast _ Hadd. split; [| intros; pass; pass].
  intros s t' _ m' started' Hst. destruct (Z_lt_le_dec wa m') as [Hlt | Hle]; [exact Hlt | exfalso].
  destruct (Z.eq_dec m' wa) as [-> | Hne]; [pose proof (makes_one Hadd Hst) as E; discriminate E |].
  (* a start before the add would be one of the five events before it *)
  pose proof (Hpast m' ltac:(lia) (makes_direct Hst)) as Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]); try contradiction; revert Hst; miss.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma startThreadAddsBeforeItStarts_Proofs_feasible : startThreadAddsBeforeItStarts_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
