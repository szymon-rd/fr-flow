Require Export FrFlowGen.OxThreads.aHerdsValsAreReadOnceItIsReady.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Scala.Tree FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** What reads a val of a herd is a method called on the herd, or a function that a call of startThread on the
    herd handed the factory. A method is called on a herd only once the herd is ready; the function was handed
    over by a call of startThread made before, on a herd that was ready then; and a herd that is ready stays so. *)
Lemma aHerdsValsAreReadOnceItIsReady_Proofs_complete : aHerdsValsAreReadOnceItIsReady_Obl_complete.
Proof.
  intros history heldIn [N C] Hreads Hconstructed Hmade h field by_ inside w Hread.
  destruct (Hreads h field by_ inside w Hread) as (i & [_ Hi] & Hby).
  assert (i <= w) as Hle by lia. apply (herd_constructed_later history h i w Hle). clear Hle.
  destruct Hby as [Hmethod | (r & (code & c & from & m & [Hm Hstart] & Hhand) & _)].
  - apply (Hconstructed h i). unfold calledOn.
    destruct Hmethod as [[[[[(x & H) | H] | (x & H)] | H] | H] | H]; apply begun_is_called in H.
    + do 5 left. eauto.
    + do 4 left. right. eauto.
    + do 3 left. right. eauto.
    + do 2 left. right. eauto.
    + left. right. eauto.
    + right. eauto.
  - assert (calledOn history h L.ThreadHerd_startThread from) as Hon
      by (unfold calledOn; eauto).
    destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
      (Hmade h from ltac:(do 5 left; exact Hon)) eq_refl Hstart) as (r0 & inside0 & Hh & Hcall0).
    destruct (method_steps C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit")
      Hcall0 Hh eq_refl) as (_ & _ & _ & _ & Hlater & _).
    pose proof (Hlater m (makes_direct Hhand)) as Hfm.
    assert (from <= i) as Hle by lia. apply (herd_constructed_later history h from i Hle).
    apply (Hconstructed h from). do 5 left. exact Hon.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
