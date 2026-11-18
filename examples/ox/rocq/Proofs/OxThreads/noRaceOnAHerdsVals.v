Require Export FrFlowGen.OxThreads.noRaceOnAHerdsVals.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Code.Conforms FrFlow.Rules.Walk.

(** A val of a herd is being written by a thread only if that thread marked it, so made the herd. Another thread
    that marks or writes it made the herd too, and a herd is made once: it is the same thread. Another thread that
    reads it does so once the herd is ready, and then no val of it is being written. *)
Lemma noRaceOnAHerdsVals_Proofs_complete : noRaceOnAHerdsVals_Obl_complete.
Proof.
  intros history heldIn [N C] Hsettled Hready Hassigned h field Hfield by_ other inside w
    [Hwriting [Hassigns | Hreads]].
  - destruct Hwriting as (m & ins & [Hm Hmark] & _).
    destruct (Hassigned h field by_ ins m (conj Hfield (or_introl Hmark))) as (m1 & cls1 & hs1 & _ & Hmade1).
    destruct (Hassigned h field other inside w (conj Hfield Hassigns)) as (m2 & cls2 & hs2 & _ & Hmade2).
    pose proof (made_at_one C Hmade1 Hmade2) as ->. rewrite Hmade1 in Hmade2.
    injection Hmade2 as -> _ _ _. reflexivity.
  - exfalso. pose proof (Hready h field other inside w (conj Hfield Hreads)) as Hr.
    destruct (Hsettled h w Hr field by_ inside w (conj Hfield (Z.le_refl w))) as [Hnot _]. exact (Hnot Hwriting).
Qed.
