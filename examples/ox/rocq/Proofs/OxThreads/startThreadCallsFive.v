Require Export FrFlowGen.OxThreads.startThreadCallsFive.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.startThread`'s tree, gone through whole: each call it makes itself is one of the five. *)
Lemma startThreadCallsFive_Proofs_complete : startThreadCallsFive_Obl_complete.
Proof.
  intros history [N C] Hmade h code from inner w (who & Hbegun & Hmakes).
  pose proof (begun_is_called _ _ _ _ Hbegun) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes) as Hdirect. revert inner Hmakes. revert w Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh
    eq_refl _).
  intros args k Hargs _. apply vals_one in Hargs as (vcode & -> & _).
  (* assertNotShuttingDown, on the herd *)
  step. intros w1 ys _ _ Hys Hinv. apply args_one in Hys as (y0 & -> & Hy0).
  pose proof (one_name N _ _ _ Hy0 Hh) as ->.
  split; [intros inner Hmk; rewrite <- (makes_one (or_introl Hinv) Hmk); auto 6 |]. intros w1' r1 sp1 x1 _ _ _.
  meets_head; [pass |].
  (* verifyCurrentThreadInScopeTree, on the herd *)
  step_rule. intros w2 ys _ _ Hys Hinv2. apply args_one in Hys as (y1 & -> & Hy1).
  pose proof (one_name N _ _ _ Hy1 Hh) as ->.
  split; [intros inner Hmk; rewrite <- (makes_one (or_introl Hinv2) Hmk); auto 6 |]. intros w2' r2 sp2 x2 _ _ _.
  meets_head; [pass |].
  (* the factory is read, and asked for a thread *)
  pass.
  step. intros w3 ys _ _ Hys Hmk3. apply args_two in Hys as (yf & yr & -> & _ & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmk3 Hmk); eauto 8 |]. intros w3' r3 x3 _ _ _ Hret3.
  meets_head; [pass |].
  (* the set is read, and the thread added to it *)
  pass.
  step. intros wadd ys _ _ Hys Hmk4. apply args_two in Hys as (ys1 & yt & -> & _ & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmk4 Hmk); eauto 8 |]. intros wadded radd xadd _ _ _ Hretadd.
  meets_head; [pass |].
  (* the thread is started, and the call returns *)
  step_rule. intros wstart ys _ _ Hys Hmk5. apply args_one in Hys as (yt' & -> & _).
  split; [intros inner Hmk; rewrite <- (makes_one Hmk5 Hmk); eauto 8 |]. intros wstarted rstart xstart _ _ _ Hretstart.
  pass.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma startThreadCallsFive_Proofs_feasible : startThreadCallsFive_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
