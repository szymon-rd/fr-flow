Require Export FrFlowGen.OxThreads.forkUserIsRefusedOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The scope supervised made is an object of the class of scopes, and its herd is closed by the moment
    supervised completes. Had a call of forkUser in it, made from then on, returned, a call of startThread on that
    herd, made after it was closed, would have returned: it does not. *)
Lemma forkUserIsRefusedOnceSupervisedEnds_Proofs_complete : forkUserIsRefusedOnceSupervisedEnds_Obl_complete.
Proof.
  intros history heldIn _ Hcloses Hstarts Hobject Hrefuses c s from to code d m fork w [[Hmade Hle] Hcalled] Hdone.
  pose proof Hmade as (supervisor & errorMode & parent & locals & code0 & ended & a & b & [_ Hmk]).
  assert (scopeMade history s) as Hs
    by exact (Hobject supervisor errorMode parent locals s a b (ex_intro _ c Hmk)).
  destruct (Hstarts code s d m fork w (conj Hs Hdone)) as (run & a1 & b1 & [Ha1 Hb1] & Hst).
  destruct (Hrefuses (heldIn "ox.OxError herd"%string s) run d d a1 b1) as [Hnot _]; [| exact (Hnot Hst)].
  split.
  - destruct (Hcloses c s from to Hmade) as (f0 & e0 & t0 & Ht0 & Hclosed).
    exists f0, e0, t0. split; [lia | exact Hclosed].
  - destruct Hst as [[(ins & sp & Hat) _] | [Hbegun _]]; [| left; exact Hbegun].
    right. exists (Response_Returned Value_Unit_), ins, sp. exact Hat.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma forkUserIsRefusedOnceSupervisedEnds_Proofs_feasible : forkUserIsRefusedOnceSupervisedEnds_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter), (fun _ x => x).
  split; [exact rest_runs |].
  split.
  { intros c s from to (supervisor & errorMode & parent & locals & code & ended & a & b & [[H _] _]).
    destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros code s c from fork to [_ H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros supervisor errorMode parent locals s from to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h code c t from w [(f0 & e0 & t0 & _ & H) _]. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
