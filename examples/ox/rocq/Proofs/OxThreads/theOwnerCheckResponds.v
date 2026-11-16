Require Export FrFlowGen.OxThreads.theOwnerCheckResponds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic FrFlow.Code.Live.

(** Proven of `ThreadHerd.assertOnOwnerThread`'s tree: given its turn, it asks for the current thread, which is
    responded to, reads the herd's owner, and returns or throws. *)
Lemma theOwnerCheckResponds_Proofs_complete : theOwnerCheckResponds_Obl_complete.
Proof.
  intros history [N C] Hproceeds Hcurrent Hmade h who from [Hbegun _].
  assert (calledBy history (Invocation_mk "ox.internal.ThreadHerd assertOnOwnerThread :scala.Unit" [h]) who from)
    as Hcalled by (left; exact Hbegun).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "assertOnOwnerThread" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  pose proof (proceeds_moves _ _ _ (Hproceeds h who from (or_intror Hbegun))) as Hmoves.
  refine (method_leads _ C (Member "ox.internal.ThreadHerd" "assertOnOwnerThread" ":scala.Unit") Hcall Hh eq_refl
    Hmoves _).
  intros args Hargs Hpassed. apply vals_none in Hargs as ->.
  lstep. intros wc ys Hwc Hqc Hys Hmk. apply args_none in Hys as ->.
  split.
  { intros Hinv. destruct (Hcurrent who wc (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wd rc xc Hwd Hqd Hdone Hg Hret.
  leads_head.
  { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
  lstep_rule. intros wr vown yown Hwr Hqr Hyown Htyown Hread.
  leads_head.
  all: lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]).
Qed.

Lemma theOwnerCheckResponds_Proofs_feasible : theOwnerCheckResponds_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h c i H. exfalso. repeat (destruct H as [H | H]);
      first [exact (nothing_begun_at_rest _ _ _ H) | destruct H as [x H]; exact (nothing_begun_at_rest _ _ _ H)]. }
  split.
  { intros who from [H _]. destruct (nothing_begun_at_rest _ _ _ H). }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
