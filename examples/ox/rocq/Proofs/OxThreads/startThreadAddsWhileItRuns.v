Require Export FrFlowGen.OxThreads.startThreadAddsWhileItRuns.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk.

(** A call of the code makes an event of its own only after it is made and before it responds: so the call of
    startThread that adds a thread is pending when it does. *)
Lemma startThreadAddsWhileItRuns_Proofs_complete : startThreadAddsWhileItRuns_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h code c t from w [Hcalled Hadds].
  assert (exists r, names N h (vref "ox.internal.ThreadHerd" r)) as [r Hh].
  { destruct (Hmade h code from) as (m & b & ins & hs & _ & Hmk); [| exact (made_named C Hmk)].
    left. exists c. exact Hcalled. }
  destruct Hcalled as [[inside Hcall] | (a & inside & spawns & Hat)].
  2: { exfalso. exact (method_not_atomic C
         (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hat Hh eq_refl). }
  assert (direct c from (history w)) as Hdirect.
  { destruct Hadds as [E | (a & sp & E)]; rewrite E; cbn; auto. }
  destruct (method_steps C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh
    eq_refl) as (args & at_ & _ & _ & Hlater & _ & _).
  exists from. split; [exact (Hlater _ Hdirect) |]. split; [exists inside; exact Hcall |].
  intros (k & a & sp & Hk & Hresp).
  exact (method_over C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh
    eq_refl Hresp Hk Hdirect).
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma startThreadAddsWhileItRuns_Proofs_feasible : startThreadAddsWhileItRuns_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h code w [[who H] | [who H]]; destruct (nothing_called_at_rest _ _ _ H).
Qed.
