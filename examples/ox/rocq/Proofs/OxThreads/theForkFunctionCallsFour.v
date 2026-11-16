Require Export FrFlowGen.OxThreads.theForkFunctionCallsFour.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.startThread`'s tree, twice over. The call of `newThread` that `startThread` makes
    hands the factory the function written there: `try t finally threads.remove(Thread.currentThread()).discard`.
    Run, that function calls the code, then `Thread.currentThread()`, then `remove`, then `discard` (an
    inline method, which the tree read from TASTy has as a call). *)
Lemma theForkFunctionCallsFour_Proofs_complete : theForkFunctionCallsFour_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h r c i made w
    [[(code & c0 & from0 & m & [_ Hstart] & Hhand) Hrun] Hmakes].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from0 ltac:(unfold calledOn; eauto 14)) eq_refl Hstart) as (r0 & inside0 & Hh & Hcall0).
  revert c i made w Hrun Hmakes.
  refine (method_meets
    (fun k => forall f r, itselfMakes history (Invocation_mk
      "java.util.concurrent.ThreadFactory newThread java.lang.Runnable:java.lang.Thread" [f; r]) c0 from0 k ->
      forall c i made w, calledBy history (Invocation_mk "java.lang.Runnable run :scala.Unit" [r]) c i ->
      itselfMakes history made c i w ->
      (((exists code, made = Invocation_mk "scala.Function0 apply :java.lang.Object" [code]) \/
        made = Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" []) \/
      exists s t, made = Invocation_mk
        "java.util.concurrent.ConcurrentHashMap$.KeySetView remove java.lang.Object:scala.Boolean" [s; t]) \/
      exists x, made = Invocation_mk "ox.util$package$ discard 1,java.lang.Object:scala.Unit" [x])
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall0 Hh eq_refl _ m
    (makes_direct Hhand) _ r Hhand).
  intros args k Hargs Hpassed. apply vals_one in Hargs as (vcode & -> & _).
  inversion Hpassed as [| p v ps vs Hp _]; subst. lazy in Hp. destruct Hp as (body & sc0 & ->).
  pass. pass. pass.
  step. intros wn ysn _ _ Hysn Hmk. split; [| intros; pass; pass; pass; pass].
  intros f r' Hit c i made w Hrun Hmakes. pose proof (makes_one Hmk Hit) as E. injection E as ->.
  apply args_two in Hysn as (yf & yr & E & _ & Hr). injection E as <- <-.
  lazymatch type of Hr with names _ _ (VCode ?fn) =>
    assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  destruct Hrun as [[inside Hcall] | (a & inside & sp & Hat)];
    [| exfalso; exact (function_not_atomic C Hat eq_refl Hr Hwritten)].
  pose proof (makes_direct Hmakes) as Hdirect. revert made Hmakes. revert w Hdirect.
  refine (function_meets _ C Hcall eq_refl Hr Hwritten _).
  intros args' k' Hargs' _. apply vals_none in Hargs' as ->.
  (* it calls the code it was made to run *)
  step. intros wt mt yt yst Hwt _ Hcalledas Hyt Hyst Hmkt.
  cbv beta iota delta [called_as] in Hcalledas. subst mt. inversion Hyst; subst.
  split; [intros made Hitmk; rewrite <- (makes_one (or_introl Hmkt) Hitmk); left; left; left; eexists; reflexivity |].
  intros wtd rt spt xt Hwtd Hresp Hgives.
  (* whatever that gave, the herd's set is read *)
  pass.
  (* Thread.currentThread() *)
  all: step; intros wc ysc Hwc _ Hysc Hmkc; apply args_none in Hysc as ->;
    (split; [intros made Hitmk; rewrite <- (makes_one Hmkc Hitmk); left; left; right; reflexivity |]);
    intros wd acur xcur Hwd Hcur Hgivescur Htycur.
  (* it threw: so does the function; it returned: remove is called, and nothing after *)
  all: step; [miss |]; intros wr ysr Hwr _ Hysr Hrm;
    apply args_two in Hysr as (yset & yt' & -> & _ & _);
    (split; [intros made Hitmk; rewrite <- (makes_one Hrm Hitmk); left; right; eauto |]);
    intros wrd arem xrem Hwrd Hrem Hgivesrem Htyrem.
  (* it threw: so does the function; it returned: what it gave is discarded *)
  all: step; [miss |]; intros wdis ysdis Hwdis _ Hysdis Hmkdis; cbn in Hysdis;
    apply args_one in Hysdis as (ydis & -> & _);
    (split; [intros made Hitmk; rewrite <- (makes_one Hmkdis Hitmk); right; eauto | intros; repeat pass]).
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma theForkFunctionCallsFour_Proofs_feasible : theForkFunctionCallsFour_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
