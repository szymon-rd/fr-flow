Require Export FrFlowGen.OxThreads.supervisedClosesItsScopesHerd.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** The call of supervised ran the code in the scope it made, and that completed only after closing the scope's herd
    had: by the thread that made the scope, which is the herd's owner. So the herd is closed by the moment
    supervised completes. *)
Lemma supervisedClosesItsScopesHerd_Proofs_complete : supervisedClosesItsScopesHerd_Obl_complete.
Proof.
  intros heldIn history _ Hruns Hends Howner c s from to Hmade.
  destruct (Hruns c s from to Hmade) as (g & a2 & ran & b2 & [Hit Hran] & Hb2).
  destruct Hmade as (supervisor & errorMode & parent & locals & code & ended & a & b & [[Hdone Hmakes] Hmk]).
  destruct (Hends s g c a2 ran b2 Hran) as (a3 & closing & b3 & [Ha3 Hb3] & Hclosing).
  pose proof (Howner supervisor errorMode parent locals c s a b Hmk) as Eowner.
  exists a3, closing, b3. split; [lia | rewrite Eowner; exact Hclosing].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma supervisedClosesItsScopesHerd_Proofs_feasible : supervisedClosesItsScopesHerd_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros c s from to (supervisor & errorMode & parent & locals & code & ended & a & b & [[H _] _]).
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s code c from ended to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros supervisor errorMode parent locals c s from to H. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
