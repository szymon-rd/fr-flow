Require Export FrFlowGen.OxThreads.whatAForkBeganIsOverOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia Classical.

(** The fork's call of its code was pending when the call was begun. Once the herd is closed it is pending no
    more: so it is over, and what was begun during it was over before. *)
Lemma whatAForkBeganIsOverOnceClosed_Proofs_complete : whatAForkBeganIsOverOnceClosed_Obl_complete.
Proof.
  intros heldIn history _ Hnone Hnest h t forked inner m w
    [[[Hclosed Hmade] (m0 & Hm0 & Hbegun & Hpending)] Hinner].
  destruct Hclosed as (cf & ce & ct & Hct & Hclosing).
  destruct Hmade as (c0 & f0 & added & t0 & [Ht0 Hadd] & Hstarting).
  destruct (Z_lt_le_dec m w) as [Hbefore | Hafter].
  - destruct (Hnone h t forked w) as [Hnot _].
    { split; [exists cf, ce, ct; split; [exact Hct | exact Hclosing] |].
      exists c0, f0, added, t0. split; [split; [lia | exact Hadd] | exact Hstarting]. }
    apply (Hnest t (Invocation_mk "scala.Function0 apply :java.lang.Object"%string [forked]) m0 inner m w).
    split; [split; [split; [split |] |] |]; try assumption.
    apply NNPP. intros Hstill. apply Hnot. exists m0. split; [lia | split; [exact Hbegun | exact Hstill]].
  - exfalso. destruct (Hnone h t forked m) as [Hnot _].
    { split; [exists cf, ce, ct; split; [lia | exact Hclosing] |].
      exists c0, f0, added, t0. split; [split; [exact Ht0 | exact Hadd] | exact Hstarting]. }
    apply Hnot. exists m0. split; [exact Hm0 | split; [exact Hbegun | exact Hpending]].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma whatAForkBeganIsOverOnceClosed_Proofs_feasible : whatAForkBeganIsOverOnceClosed_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h t code w [(from & ended & to & _ & H) _]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros by_ outer from inner m e [[[[H _] _] _] _]. destruct (nothing_begun_at_rest _ _ _ H).
Qed.
