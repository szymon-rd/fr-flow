Require Export FrFlowGen.OxThreads.codeRunsBeforeLeaving.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The code is called only by the function startThread handed the factory, run by the fork; the fork is removed
    only by itself, in such a function; a thread runs one such function, once; and that function removes only
    after its call of the code has been responded to. *)
Lemma codeRunsBeforeLeaving_Proofs_complete : codeRunsBeforeLeaving_Obl_complete.
Proof.
  intros heldIn history _ Hcalls Honce Hafter Hself Hrem Hconstructed h t code made w Hmade.
  assert (exists m0, exists who, calledBy history (Invocation_mk
    L.ThreadHerd_startThread [h; code]) who m0) as (m0 & Hst).
  { destruct Hmade as (c & from & added & to & _ & (m0 & _ & Hb & _)). exists m0, c. left. exact Hb. }
  pose proof Hst as (starter & Hstarting).
  pose proof (Hconstructed h m0 ltac:(unfold calledOn; eauto 14)) as Hherd.
  split.
  - intros Hcode (k & Hk & who & Hremoved). pose proof (Hself h t who k m0 (conj Hherd Hremoved)) as ->.
    destruct (Hrem h t t k m0 (conj Hherd Hremoved)) as (r2 & i2 & [Hh2 Hr2] & Hit2).
    destruct (Hcalls h code t m0 w (conj Hst Hcode)) as (r1 & i1 & [Hh1 Hr1] & Hit1).
    pose proof (Honce h h r1 r2 t i1 i2 (conj (conj (conj Hh1 Hr1) Hh2) Hr2)) as ->.
    destruct (Hafter h r1 t code t i2 w k (conj (conj (conj Hh1 Hr1) Hit1) Hit2)) as [Hwk _]. lia.
  - intros (who & Hremoved) (m & Hm & Hb & Hn). pose proof (Hself h t who w m0 (conj Hherd Hremoved)) as ->.
    destruct (Hrem h t t w m0 (conj Hherd Hremoved)) as (r2 & i2 & [Hh2 Hr2] & Hit2).
    destruct (Hcalls h code t m0 m (conj Hst (or_introl Hb))) as (r1 & i1 & [Hh1 Hr1] & Hit1).
    pose proof (Honce h h r1 r2 t i1 i2 (conj (conj (conj Hh1 Hr1) Hh2) Hr2)) as ->.
    destruct (Hafter h r1 t code t i2 m w (conj (conj (conj Hh1 Hr1) Hit1) Hit2)) as [Hmw Hnot].
    apply Hnot. split; [exact Hmw | split; [exact Hb | exact Hn]].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
