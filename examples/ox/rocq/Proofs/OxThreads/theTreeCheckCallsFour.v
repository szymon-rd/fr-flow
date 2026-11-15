Require Export FrFlowGen.OxThreads.theTreeCheckCallsFour.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.verifyCurrentThreadInScopeTree`'s tree, gone through whole: it asks for the current
    thread and for the scope of the thread; with no scope it asks the thread's name and throws; with one it
    applies its own function to it. *)
Lemma theTreeCheckCallsFour_Proofs_complete : theTreeCheckCallsFour_Obl_complete.
Proof.
  intros history [N C] Hmade h from inner w (who & Hbegun & Hmakes).
  pose proof (begun_is_called _ _ _ _ Hbegun) as Hcalled.
  destruct (method_begun (Member "ox.internal.ThreadHerd" "verifyCurrentThreadInScopeTree" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (makes_direct Hmakes) as Hdirect. revert inner Hmakes. revert w Hdirect.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "verifyCurrentThreadInScopeTree" ":scala.Unit")
    Hcall Hh eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* Thread.currentThread() *)
  step. intros wcur ys _ _ Hys Hmk1. apply args_none in Hys as ->.
  split; [intros inner Hmk; rewrite <- (makes_one Hmk1 Hmk); auto 6 |]. intros wcur' rcur xcur _ _ _ Hretcur.
  meets_head; [pass |].
  (* the scope of the thread *)
  step_rule. intros wget ys _ _ Hys Hmk2. apply args_none in Hys as ->.
  split; [intros inner Hmk; rewrite <- (makes_one Hmk2 Hmk); auto 6 |]. intros wget' rget xget _ _ _ Hretget.
  meets_head; [pass | |].
  - (* no scope: the thread and its name are asked, and the check throws *)
    step_rule. intros wagain ys _ _ Hys Hmk3. apply args_none in Hys as ->.
    split; [intros inner Hmk; rewrite <- (makes_one Hmk3 Hmk); auto 6 |].
    intros wagain' ragain xagain _ _ _ Hretagain.
    meets_head; [pass |].
    step_rule. intros wname ys _ _ Hys Hmk4. apply args_one in Hys as (yt & -> & _).
    split; [intros inner Hmk; rewrite <- (makes_one Hmk4 Hmk); eauto 8 |]. intros wname' rname xname _ _ _ Hretname.
    pass.
  - (* a scope: the check applies its own function to it *)
    step_rule. intros wapp m yf ys _ _ Hm Hyf Hys Hinv. cbv [called_as] in Hm. subst m.
    apply args_one in Hys as (yscope & -> & _).
    split; [intros inner Hmk; rewrite <- (makes_one (or_introl Hinv) Hmk); eauto 8 |].
    intros wapp' rapp spapp xapp _ _ _. pass.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma theTreeCheckCallsFour_Proofs_feasible : theTreeCheckCallsFour_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
