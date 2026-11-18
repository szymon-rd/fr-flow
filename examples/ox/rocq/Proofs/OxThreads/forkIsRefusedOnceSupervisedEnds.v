Require Export FrFlowGen.OxThreads.forkIsRefusedOnceSupervisedEnds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The scope supervised made is an object of the class of scopes, and its herd is closed by the moment
    supervised completes. Had a call of fork in it, made from then on, returned, a call of startThread on that
    herd, made after it was closed, would have returned: it does not. *)
Lemma forkIsRefusedOnceSupervisedEnds_Proofs_complete : forkIsRefusedOnceSupervisedEnds_Obl_complete.
Proof.
  intros history heldIn _ Hcloses Hstarts Hobject Hrefuses c s from to Hmade code d m fork w [Hle Hcalled] Hdone.
  pose proof Hmade as (supervisor & errorMode & parent & locals & code0 & ended & a & b & [_ Hmk]).
  assert (scopeMade history s) as Hs
    by exact (Hobject supervisor errorMode parent locals s a b (ex_intro _ c Hmk)).
  destruct (Hstarts code s d m fork w (conj Hs Hdone)) as (run & a1 & b1 & [Ha1 Hb1] & Hst).
  destruct (Hrefuses (heldIn L.OxError_herd s) to (Hcloses c s from to Hmade) run d d a1 b1) as [Hnot _];
    [| exact (Hnot Hst)].
  split; [lia |].
  destruct Hst as [[(ins & sp & Hat) _] | [Hbegun _]]; [| left; exact Hbegun].
  right. exists (Response_Returned Value_Unit_), ins, sp. exact Hat.
Qed.
