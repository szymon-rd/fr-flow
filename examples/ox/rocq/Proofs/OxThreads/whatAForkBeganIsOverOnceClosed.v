Require Export FrFlowGen.OxThreads.whatAForkBeganIsOverOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia Classical.

(** The fork's call of its code was pending when the call was begun. Once the herd is closed it is pending no
    more: so it is over, and what was begun during it was over before. *)
Lemma whatAForkBeganIsOverOnceClosed_Proofs_complete : whatAForkBeganIsOverOnceClosed_Obl_complete.
Proof.
  intros heldIn history _ Hnone Hnest h w Hclosed t forked inner m
    [[Hmade (m0 & Hm0 & Hbegun & Hpending)] Hinner].
  destruct Hmade as (c0 & f0 & added & t0 & [Ht0 Hadd] & Hstarting).
  destruct (Z_lt_le_dec m w) as [Hbefore | Hafter].
  - destruct (Hnone h w Hclosed t forked w) as [Hnot _].
    { split; [lia |]. exists c0, f0, added, t0. split; [split; [lia | exact Hadd] | exact Hstarting]. }
    apply (Hnest t (Invocation_mk L.Function0_apply [forked]) m0 inner m w).
    split; [split; [split; [split |] |] |]; try assumption.
    apply NNPP. intros Hstill. apply Hnot. exists m0. split; [lia | split; [exact Hbegun | exact Hstill]].
  - exfalso. destruct (Hnone h w Hclosed t forked m) as [Hnot _].
    { split; [exact Hafter |]. exists c0, f0, added, t0. split; [split; [exact Ht0 | exact Hadd] | exact Hstarting]. }
    apply Hnot. exists m0. split; [exact Hm0 | split; [exact Hbegun | exact Hpending]].
Qed.
