Require Export FrFlowGen.OxThreads.anInterruptedForkLeavesForGood.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The thread was added by a call of startThread on the herd, itself: a factory made it for that call, for a
    function; the call has called start on it; it runs the function, which ends once the code it calls does, the
    thread having been interrupted. The function is one startThread handed a factory: once it has completed, the
    thread is out of the herd's set for good. *)
Lemma anInterruptedForkLeavesForGood_Proofs_complete : anInterruptedForkLeavesForGood_Obl_complete.
Proof.
  intros elements heldIn history _ Hstarts Hruns Hcompletes Hcode Hout Honly Hwhile Hfactory Hconstructed
    h t code made [Hmade Hint].
  destruct Hmade as (c & afrom & added & ato & [Hto Hadded] & (m0 & Hm0 & Hbegun0 & Hnotover0)).
  pose proof (begun_is_called _ _ _ _ Hbegun0) as Hcalled0.
  assert (ready heldIn history h afrom) as Hcons.
  { apply (herd_constructed_later history h m0 afrom ltac:(lia)). apply (Hconstructed h m0).
    do 5 left. unfold calledOn. eauto 14. }
  destruct (Honly h t c afrom afrom (conj Hcons (completed_was_called _ _ _ _ _ _ Hadded)))
    as (code' & from' & Hcalled' & Hadds').
  assert (madeToRun heldIn history t h code' ato) as Hmade'.
  { exists c, afrom, added, ato. split; [split; [lia | exact Hadded] |].
    exact (Hwhile h code' c t from' afrom (conj Hcalled' Hadds')). }
  destruct (Hfactory h code' c t from' afrom (conj Hcalled' Hadds')) as (f & r & a0 & done & [Hdone Hnew] & Hnewdone).
  destruct (Hstarts h code' c t from' afrom added ato (conj (conj Hcalled' Hadds') Hadded)) as (ms & Hstart).
  assert (calledBy history (Invocation_mk L.Thread_start [t]) c ms) as Hstarted.
  { destruct Hstart as [E | (rs & sps & E)]; [left; exists (Some from'); exact E |].
    right. exists rs, (Some from'), sps. exact E. }
  destruct (Hruns f r t a0 done ms (conj (ex_intro _ c Hnewdone) (ex_intro _ c Hstarted))) as (i & Hai & Hrun).
  assert (forkFunction history r h code') as Hfork.
  { exists c, from', f, a0. split; [exact Hcalled' | exact Hnew]. }
  (* the function ends, the code it calls being responded to *)
  destruct (Hcompletes h r code' t i) as [Hbegun (to & k & ended & sp & Hk & Hended)].
  { split; [split; [exact Hfork | exact Hrun] |].
    intros m Hm. apply (Hcode h t code' ato m). split; [split; [exact Hmade' |] | exact Hint].
    destruct Hm as [E | (rs & sps & E)]; [left; exists (Some i); exact E |].
    right. exists rs, (Some i), sps. exact E. }
  (* and from then on the thread is out of the set *)
  exists (k + 1). intros w Hw. apply (Hout h r code' t i ended (k + 1) w afrom).
  split; [split; [split; [exact Hcons | exact Hfork] |] | exact Hw].
  right. split; [exact Hbegun |]. exists sp. replace (k + 1 - 1) with k by lia. exact Hended.
Qed.
