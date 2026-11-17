Require Export FrFlowGen.OxThreads.aForkEndsOnceInterrupted.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The thread was added by a call of startThread on the herd, itself: so a factory made it for that call, for a
    function; the call has called start on it; and so it runs the function, which ends once the code it calls
    does. The code is what startThread was given, which the thread was made to run: it ends, the thread having
    been interrupted. *)
Lemma aForkEndsOnceInterrupted_Proofs_complete : aForkEndsOnceInterrupted_Obl_complete.
Proof.
  intros heldIn history _ Hstarts Hruns Hcompletes Hcode Honly Hwhile Hfactory Hconstructed
    h t code made [Hmade Hint].
  destruct Hmade as (c & afrom & added & ato & [Hto Hadded] & (m0 & Hm0 & Hbegun0 & Hnotover0)).
  (* the herd has been made: startThread was called on it *)
  pose proof (begun_is_called _ _ _ _ Hbegun0) as Hcalled0.
  assert (ready heldIn history h afrom) as Hcons.
  { apply (herd_constructed_later history h m0 afrom ltac:(lia)). apply (Hconstructed h m0).
    do 5 left. unfold calledOn. eauto 14. }
  (* the add was made by a call of startThread on the herd, itself *)
  destruct (Honly h t c afrom afrom (conj Hcons (completed_was_called _ _ _ _ _ _ Hadded)))
    as (code' & from' & Hcalled' & Hadds').
  assert (madeToRun heldIn history t h code' ato) as Hmade'.
  { exists c, afrom, added, ato. split; [split; [lia | exact Hadded] |].
    exact (Hwhile h code' c t from' afrom (conj Hcalled' Hadds')). }
  (* the thread is one a factory made for the call, for a function *)
  destruct (Hfactory h code' c t from' afrom (conj Hcalled' Hadds')) as (f & r & a0 & done & [Hdone Hnew] & Hnewdone).
  (* start is called on it, and it runs the function *)
  destruct (Hstarts h code' c t from' afrom added ato (conj (conj Hcalled' Hadds') Hadded)) as (ms & Hstart).
  assert (calledBy history (Invocation_mk "java.lang.Thread start :scala.Unit"%string [t]) c ms) as Hstarted.
  { destruct Hstart as [E | (rs & sps & E)]; [left; exists (Some from'); exact E |].
    right. exists rs, (Some from'), sps. exact E. }
  destruct (Hruns f r t a0 done ms (conj (ex_intro _ c Hnewdone) (ex_intro _ c Hstarted))) as (i & Hai & Hrun).
  (* which ends, the code it calls being responded to *)
  exists f, r, a0, done, i. split; [exists c; exact Hnewdone |].
  apply (Hcompletes h r code' t i). split; [split; [| exact Hrun] |].
  - exists c, from', f, a0. split; [exact Hcalled' | exact Hnew].
  - intros m Hm. apply (Hcode h t code' ato m). split; [split; [exact Hmade' |] | exact Hint].
    destruct Hm as [E | (rs & sps & E)]; [left; exists (Some i); exact E |].
    right. exists rs, (Some i), sps. exact E.
Qed.

(** What it is from can hold: an execution in which nothing happens meets each. *)
Lemma aForkEndsOnceInterrupted_Proofs_feasible : aForkEndsOnceInterrupted_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h code c t from a added b [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros f r t a b s [[who H] _]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h r code t i [[_ H] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h t code made m [[_ H] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h t c w b [_ H]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
