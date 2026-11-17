Require Export FrFlowGen.OxThreads.aForkFunctionRemovesItsThread.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.startThread`'s tree, twice over. The function it hands the factory is the one written
    there, `try t finally threads.remove(Thread.currentThread()).discard`. Whatever the code gave, it reads the
    herd's set, asks for the current thread, which is its caller, and calls `remove` on the set with it; it ends
    only after that call is responded to. *)
Lemma aForkFunctionRemovesItsThread_Proofs_complete : aForkFunctionRemovesItsThread_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hfields Hcurrent h r code t i ended e [Hfork Hrun].
  destruct Hfork as (c0 & from0 & f0 & m & Hstart & Hhand).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from0 ltac:(unfold calledOn; eauto 14)) eq_refl Hstart) as (r0 & inside0 & Hh & Hcall0).
  revert t i ended e Hrun.
  refine (method_meets
    (fun j => forall f r, itselfMakes history (Invocation_mk
      "java.util.concurrent.ThreadFactory newThread java.lang.Runnable:java.lang.Thread" [f; r]) c0 from0 j ->
      forall t i ended e, completedBy history (Invocation_mk "java.lang.Runnable run :scala.Unit" [r]) t i ended e ->
      exists a b, completedBy history
        (Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" []) t a (Response_Returned t) b /\
        exists a1 rr b1, (b <= a1 /\ b1 <= e) /\ completedBy history (Invocation_mk
          "java.util.concurrent.ConcurrentHashMap$.KeySetView remove java.lang.Object:scala.Boolean"
          [heldIn "ox.internal.ThreadHerd threads" h; t]) t a1 rr b1)
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall0 Hh eq_refl _ m
    (makes_direct Hhand) _ r Hhand).
  intros args j Hargs Hpassed. apply vals_one in Hargs as (vcode & -> & Hnamed).
  inversion Hpassed as [| p v ps vs Hp _]; subst. lazy in Hp. destruct Hp as (body & sc0 & ->).
  (* the two checks; the factory is read *)
  pass. pass. pass.
  (* and handed a function: the one written here; what follows hands over none *)
  step. intros wn ysn _ _ Hysn Hmk. split; [| intros; pass; pass; pass; pass].
  intros f r' Hit t i ended e Hrun. pose proof (makes_one Hmk Hit) as E. injection E as ->.
  apply args_two in Hysn as (yf & yr & E & _ & Hr). injection E as <- <-.
  lazymatch type of Hr with names _ _ (VCode ?fn) =>
    assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  destruct Hrun as [[(ins1 & sp1 & Hat1) _] | [[inside1 Hcall1] [sp1 Hend1]]];
    [exfalso; exact (function_not_atomic C Hat1 eq_refl Hr Hwritten) |].
  assert (direct t i (history (e - 1))) as Hdir1 by (rewrite Hend1; cbn; auto).
  remember (e - 1) as last eqn:Elast. assert (e = last + 1) as -> by lia. clear Elast.
  revert ended sp1 Hend1. revert Hdir1. revert last.
  refine (function_meets _ C Hcall1 eq_refl Hr Hwritten _).
  intros args' k' Hargs' _. apply vals_none in Hargs' as ->.
  (* it calls the code it was made to run; whatever that gave, the herd's set is read: the set the herd holds *)
  pass.
  step.
  all: intros wr vset yset Hwr _ Hyset Htyset Hread; (split; [miss |]).
  all: apply (proj2 (Hfields h)) in Hread; subst yset.
  (* the current thread is asked for: it is the caller *)
  all: step; intros wc ysc Hwc _ Hysc Hmkc; (split; [miss |]); intros wd rcur xcur Hwd Hcur Hgives Hty.
  all: apply args_none in Hysc as ->.
  all: pose proof (Hcurrent t wc rcur wd (done_completed Hcur)) as Ecur; subst rcur.
  all: destruct xcur as [ecur | vcur]; [contradiction |].
  (* and removed from the set, by a call the function waits for *)
  all: step; intros wm ysm Hwm _ Hysm Hmkm; (split; [miss |]); intros wmd rrm xm Hwmd Hrem Hgivesm Htym.
  all: apply args_two in Hysm as (yrset & yrthread & -> & Hyrset & Hyrthread).
  all: pose proof (one_name N _ _ _ Hyrset Hyset) as ->; pose proof (one_name N _ _ _ Hyrthread Hgives) as ->.
  (* what follows makes no event the claim speaks of, up to the end *)
  all: meets_head.
  all: try (step_rule; intros wdc ysdc Hwdc _ Hysdc Hmkdc; (split; [miss |]);
    intros wdd rd xd Hwdd Hdisc Hgivesd Htyd).
  all: meets_head.
  all: apply meets_ret; intros rr0 Hk0 _ Hrr0 Hgives0 ended sp Hresp.
  all: exists wc, wd; (split; [exact (done_completed Hcur) |]); exists wm, rrm, wmd.
  all: split; [split; lia | exact (done_completed Hrem)].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma aForkFunctionRemovesItsThread_Proofs_feasible : aForkFunctionRemovesItsThread_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H). }
  split.
  { intros h. repeat split; intros w by_ inside found H; discriminate H. }
  intros c from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H).
Qed.
