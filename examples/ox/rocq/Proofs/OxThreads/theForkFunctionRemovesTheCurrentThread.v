Require Export FrFlowGen.OxThreads.theForkFunctionRemovesTheCurrentThread.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.startThread`'s tree, twice over. The call of `newThread` that `startThread` makes
    hands the factory the function written there: `try t finally threads.remove(Thread.currentThread()).discard`.
    Run, that function calls `remove` once, with what `Thread.currentThread()` has just given it. *)
Lemma theForkFunctionRemovesTheCurrentThread_Proofs_complete :
  theForkFunctionRemovesTheCurrentThread_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hfields h r c t i w
    [[(code & c0 & from0 & m & [_ Hstart] & Hhand) Hrun] Hrem].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from0 ltac:(unfold calledOn; eauto 14)) eq_refl Hstart) as (r0 & inside0 & Hh & Hcall0).
  revert c t i w Hrun Hrem.
  refine (method_meets
    (fun k => forall f r, itselfMakes history (Invocation_mk
      "java.util.concurrent.ThreadFactory newThread java.lang.Runnable:java.lang.Thread" [f; r]) c0 from0 k ->
      forall c t i w, calledBy history (Invocation_mk "java.lang.Runnable run :scala.Unit" [r]) c i ->
      itselfMakes history (Invocation_mk
        "java.util.concurrent.ConcurrentHashMap$.KeySetView remove java.lang.Object:scala.Boolean"
        [heldIn "ox.internal.ThreadHerd threads" h; t]) c i w ->
      exists a b, (i < a /\ b <= w) /\ completedBy history
        (Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" []) c a (Response_Returned t) b)
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall0 Hh eq_refl _ m
    (makes_direct Hhand) _ r Hhand).
  intros args k Hargs Hpassed. apply vals_one in Hargs as (vcode & -> & _).
  (* what startThread is given by name is a function *)
  inversion Hpassed as [| p v ps vs Hp _]; subst. lazy in Hp. destruct Hp as (body & sc0 & ->).
  (* the two checks; the factory is read *)
  pass. pass. pass.
  (* and handed a function: the one written here; what follows hands over none *)
  step. intros wn ysn _ _ Hysn Hmk. split; [| intros; pass; pass; pass; pass].
  intros f r' Hit c t i w Hrun Hrem. pose proof (makes_one Hmk Hit) as E. injection E as ->.
  apply args_two in Hysn as (yf & yr & E & _ & Hr). injection E as <- <-.
  (* a thread runs it *)
  lazymatch type of Hr with names _ _ (VCode ?fn) =>
    assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  destruct Hrun as [[inside Hcall] | (a & inside & sp & Hat)];
    [| exfalso; exact (function_not_atomic C Hat eq_refl Hr Hwritten)].
  refine (function_meets
    (fun k => forall s t, itselfMakes history (Invocation_mk
      "java.util.concurrent.ConcurrentHashMap$.KeySetView remove java.lang.Object:scala.Boolean" [s; t]) c i k ->
      exists a b, (i < a /\ b <= k) /\ completedBy history
        (Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" []) c a (Response_Returned t) b)
    C Hcall eq_refl Hr Hwritten _ w (makes_direct Hrem) _ t Hrem).
  intros args' k' Hargs'. apply vals_none in Hargs' as ->.
  (* it calls the code it was made to run; whatever that gave, the herd's set is read *)
  pass. pass.
  (* Thread.currentThread() *)
  all: step; intros wc ysc Hwc _ Hysc Hmkc; (split; [miss |]); intros wd a x Hwd Hcur Hgives Hty.
  (* it threw: so does the function; it returned: remove is called, with what it gave; nothing is removed after *)
  all: step; [miss |]; intros wr ysr Hwr _ Hysr Hrm; (split; [| intros; pass; pass]).
  all: intros s t' Hit'; pose proof (makes_one Hrm Hit') as E; injection E as ->.
  all: apply args_two in Hysr as (yset & yt & E & _ & Hyt); injection E as <- <-.
  all: destruct a as [made | thrown]; [| contradiction]; rewrite (one_name N _ _ _ Hyt Hgives).
  all: apply args_none in Hysc as ->; exists wc, wd; (split; [lia | exact (done_completed Hcur)]).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma theForkFunctionRemovesTheCurrentThread_Proofs_feasible :
  theForkFunctionRemovesTheCurrentThread_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H). }
  intros h. repeat split; intros w by_ inside found H; discriminate H.
Qed.
