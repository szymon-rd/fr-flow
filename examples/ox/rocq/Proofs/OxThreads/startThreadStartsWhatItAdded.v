Require Export FrFlowGen.OxThreads.startThreadStartsWhatItAdded.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.

(** Proven of `ThreadHerd.startThread`'s tree. A call that is seen to add a thread has got there: each call it
    made before was responded to. The call that adds is responded to in time, and the thread that runs
    startThread, given its turn, calls start next: on the thread it added, the call adding but once. *)
Lemma startThreadStartsWhatItAdded_Proofs_complete : startThreadStartsWhatItAdded_Obl_complete.
Proof.
  intros heldIn history [N C] Honce Hproceeds Hmade h code c t from a added b [[Hcalled Hadds] Hadded].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  assert (moves history c from) as Hmoves.
  { apply proceeds_moves. apply (Hproceeds h c from). do 5 left. exists code, inside. exact Hcall. }
  pose proof (makes_direct Hadds) as Hdir.
  assert (from + 1 <= a) as Hahead.
  { destruct (method_steps C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl) as (_ & _ & _ & _ & Hlater & _).
    pose proof (Hlater a Hdir). lia. }
  refine (method_leads _ C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl Hmoves _).
  intros args Hargs Hpassed. apply vals_one in Hargs as (vcode & -> & _).
  inversion Hpassed as [| p v ps vs Hp _]; subst. lazy in Hp. destruct Hp as (body & sc0 & ->).
  leads_head.
  (* the check that the herd is not closing: responded to, the add being still ahead *)
  lstep_rule. intros w1 ys1 Hw1 Hq1 Hys1 Hinv1.
  assert (w1 + 1 <= a) as Ha1.
  { apply (ahead_other Hq1 Hahead Hdir). intros ->.
    destruct Hadds as [E | (? & ? & E)]; rewrite Hinv1 in E; discriminate E. }
  split; [apply responded_ahead with (later := a); [lia | exact Hdir] |].
  intros w1d r1 sp1 x1 Hw1d Hq1d He1 Hg1 Hret1.
  pose proof (ahead_answered Hadds Ha1 Hq1d He1) as Ha1d. clear Hahead. rename Ha1d into Hahead.
  leads_head.
  all: try (lstep_rule; intros w9 r9 Hw9 Hq9 He9 Hg9; exfalso;
    pose proof (ahead_quiet Hq9 Hahead Hdir) as Hle9;
    assert (a <> w9) as Hne9 by (intros ->; destruct Hadds as [E | (? & ? & E)]; rewrite He9 in E; discriminate E);
    exact (method_over C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl He9 (w := a) ltac:(lia) Hdir)).
  (* the check of the tree of scopes, the same *)
  lstep_rule. intros w2 ys2 Hw2 Hq2 Hys2 Hinv2.
  assert (w2 + 1 <= a) as Ha2.
  { apply (ahead_other Hq2 Hahead Hdir). intros ->.
    destruct Hadds as [E | (? & ? & E)]; rewrite Hinv2 in E; discriminate E. }
  split; [apply responded_ahead with (later := a); [lia | exact Hdir] |].
  intros w2d r2 sp2 x2 Hw2d Hq2d He2 Hg2 Hret2.
  pose proof (ahead_answered Hadds Ha2 Hq2d He2) as Ha2d. clear Hahead. rename Ha2d into Hahead.
  leads_head.
  all: try (lstep_rule; intros w9 r9 Hw9 Hq9 He9 Hg9; exfalso;
    pose proof (ahead_quiet Hq9 Hahead Hdir) as Hle9;
    assert (a <> w9) as Hne9 by (intros ->; destruct Hadds as [E | (? & ? & E)]; rewrite He9 in E; discriminate E);
    exact (method_over C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl He9 (w := a) ltac:(lia) Hdir)).
  (* the factory is read *)
  lstep_rule. intros w3 v3 y3 Hw3 Hq3 Hy3 Hty3 Hread3.
  assert (w3 + 1 <= a) as Ha3.
  { apply (ahead_other Hq3 Hahead Hdir). intros ->.
    destruct Hadds as [E | (? & ? & E)]; rewrite Hread3 in E; discriminate E. }
  clear Hahead. rename Ha3 into Hahead.
  leads_head.
  (* and asked for a thread *)
  lstep_rule. intros w4 ys4 Hw4 Hq4 Hys4 Hmk4.
  assert (w4 + 1 <= a) as Ha4.
  { apply (ahead_other Hq4 Hahead Hdir). intros ->. pose proof (makes_one Hmk4 Hadds) as E. discriminate E. }
  split; [intros _; apply responded_ahead with (later := a); [lia | exact Hdir] |].
  intros w4d r4 x4 Hw4d Hq4d Hdone4 Hg4 Hret4.
  pose proof (ahead_done Hadds Ha4 Hq4d Hdone4) as Ha4d. clear Hahead. rename Ha4d into Hahead.
  leads_head.
  all: try (lstep_rule; intros w9 r9 Hw9 Hq9 He9 Hg9; exfalso;
    pose proof (ahead_quiet Hq9 Hahead Hdir) as Hle9;
    assert (a <> w9) as Hne9 by (intros ->; destruct Hadds as [E | (? & ? & E)]; rewrite He9 in E; discriminate E);
    exact (method_over C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl He9 (w := a) ltac:(lia) Hdir)).
  (* the set is read *)
  lstep_rule. intros w5 v5 y5 Hw5 Hq5 Hy5 Hty5 Hread5.
  assert (w5 + 1 <= a) as Ha5.
  { apply (ahead_other Hq5 Hahead Hdir). intros ->.
    destruct Hadds as [E | (? & ? & E)]; rewrite Hread5 in E; discriminate E. }
  clear Hahead. rename Ha5 into Hahead.
  leads_head.
  (* the thread is added: by the call of add that was seen, the one this call makes *)
  lstep_rule. intros w6 ys6 Hw6 Hq6 Hys6 Hmk6.
  apply args_two in Hys6 as (yset & yt & -> & Hyset & Hyt).
  pose proof (Honce h code c from _ t a yset yt w6 (conj (conj Hcalled Hadds) Hmk6)) as Ea. subst w6.
  pose proof (makes_one Hmk6 Hadds) as E. injection E as -> ->.
  split.
  { intros Hinv6. destruct Hadded as [[(ins & sp & Hat) _] | [_ [sp Hresp]]].
    - rewrite Hinv6 in Hat. discriminate Hat.
    - left. exists (b - 1), (Response_Returned added), sp. exact Hresp. }
  intros w6d r6 x6 Hw6d Hq6d Hdone6 Hg6 Hret6.
  pose proof (done_gave c (Response_Returned added) b C Hdone6 Hadded) as ->.
  leads_head.
  all: try (exfalso; exact Hg6).
  (* and start is called on it *)
  lstep_done. intros w7 ys7 Hw7 Hq7 Hys7 Hmk7. apply args_one in Hys7 as (y7 & -> & Hy7).
  pose proof (one_name N _ _ _ Hy7 Hyt) as ->. exists w7. exact Hmk7.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
