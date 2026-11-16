Require Export FrFlowGen.OxThreads.noForkRunsOnceUnsupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The call of unsupervised ran the code in the scope it made, and that completed only after closing the scope's
    herd had: by the thread that made the scope, which is the herd's owner. So the herd is closed by the moment
    unsupervised completes, and no fork of it runs its code from then on. *)
Lemma noForkRunsOnceUnsupervisedEnds_Proofs_complete : noForkRunsOnceUnsupervisedEnds_Obl_complete.
Proof.
  intros heldIn history _ Honceclosed Hruns Hends Howner supervisor errorMode parent locals code c s from ended to
    a b t forked w [[[[Hdone Hmakes] Hmade] Hle] Hfork].
  destruct (Hruns supervisor errorMode parent locals code c s from ended to a b (conj (conj Hdone Hmakes) Hmade))
    as (g & a2 & ran & b2 & [Hit Hran] & Hb2).
  destruct (Hends s g c a2 ran b2 Hran) as (a3 & closing & b3 & [Ha3 Hb3] & Hclosing).
  pose proof (Howner supervisor errorMode parent locals c s a b Hmade) as Eowner.
  apply (Honceclosed (heldIn "ox.OxError herd"%string s) t forked w). split; [| exact Hfork].
  exists a3, closing, b3. split; [lia | rewrite Eowner; exact Hclosing].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma noForkRunsOnceUnsupervisedEnds_Proofs_feasible : noForkRunsOnceUnsupervisedEnds_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h t code w [(from & ended & to & _ & H) _]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros supervisor errorMode parent locals code c s from ended to a b [[H _] _].
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s code c from ended to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros supervisor errorMode parent locals c s from to H. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
