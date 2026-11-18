Require Export FrFlowGen.OxThreads.startThreadAddsWhatItsFactoryMade.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.startThread`'s tree: the thread it adds to the set is the one its factory returned
    to it. *)
Lemma startThreadAddsWhatItsFactoryMade_Proofs_complete : startThreadAddsWhatItsFactoryMade_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h code c t from w [Hcalled Hadds].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  refine (method_meets
    (fun w => forall s t, itselfMakes history (Invocation_mk
      L.KeySetView_add [s; t]) c from w ->
      madeFor history t c from w)
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl _ w
    (makes_direct Hadds) _ t Hadds).
  intros args k Hargs _. apply vals_one in Hargs as (vcode & -> & _).
  (* the two checks; the factory is read *)
  pass_to L.ThreadFactory_newThread.
  (* and asked for a thread *)
  step. intros wn ysn _ _ Hysn Hmk. split; [miss |]. intros wd rn x Hwd Hnew Hgives Hty.
  (* the set is read *)
  pass.
  (* and the thread is added to it; what follows adds nothing *)
  step. intros wa ysa Hwa _ Hysa Hadd. split; [| intros; pass; pass].
  intros s t' Hit. pose proof (makes_one Hadd Hit) as E. injection E as ->.
  apply args_two in Hysa as (yset & yt & E & _ & Hyt). injection E as <- <-.
  destruct rn as [made | thrown]; [| contradiction]. rewrite (one_name N _ _ _ Hyt Hgives).
  apply args_two in Hysn as (f & rr & -> & _ & _).
  exists f, rr, wn, wd. split; [split; [lia | exact (done_made Hnew)] | exact (done_completed Hnew)].
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
