Require Export FrFlowGen.OxThreads.aForkFunctionRemovesAfterTheCode.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of `ThreadHerd.startThread`'s tree, twice over. The function it hands the factory is the one written
    there, `try t finally threads.remove(Thread.currentThread()).discard`. Run, that function first calls the
    code, and calls `remove` only once that call has been responded to; it calls no code after. *)
Lemma aForkFunctionRemovesAfterTheCode_Proofs_complete : aForkFunctionRemovesAfterTheCode_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h r c code x i w k
    [[[(code0 & c0 & from0 & m & [_ Hstart] & Hhand) Hrun] Hcode] Hrem].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from0 ltac:(unfold calledOn; eauto 14)) eq_refl Hstart) as (r0 & inside0 & Hh & Hcall0).
  revert c code x i w k Hrun Hcode Hrem.
  refine (method_meets
    (fun j => forall f r, itselfMakes history (Invocation_mk
      L.ThreadFactory_newThread [f; r]) c0 from0 j ->
      forall c code x i w k, calledBy history (Invocation_mk L.Runnable_run [r]) c i ->
      itselfMakes history (Invocation_mk L.Function0_apply [code]) c i w ->
      itselfMakes history (Invocation_mk
        L.KeySetView_remove
        [heldIn L.ThreadHerd_threads h; x]) c i k ->
      w < k /\ ~ (w < k /\ begun history (Invocation_mk L.Function0_apply [code]) c w /\
        ~ overBy history c w k))
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall0 Hh eq_refl _ m
    (makes_direct Hhand) _ r Hhand).
  intros args j Hargs Hpassed. apply vals_one in Hargs as (vcode & -> & _).
  (* what startThread is given by name is a function *)
  inversion Hpassed as [| p v ps vs Hp _]; subst. lazy in Hp. destruct Hp as (body & sc0 & ->).
  (* the two checks; the factory is read *)
  pass_to L.ThreadFactory_newThread.
  (* and handed a function: the one written here; what follows hands over none *)
  step. intros wn ysn _ _ Hysn Hmk. split; [| intros; pass; pass; pass; pass].
  intros f r' Hit c code x i w k Hrun Hcode Hrem. pose proof (makes_one Hmk Hit) as E. injection E as ->.
  apply args_two in Hysn as (yf & yr & E & _ & Hr). injection E as <- <-.
  (* a thread runs it *)
  lazymatch type of Hr with names _ _ (VCode ?fn) =>
    assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  destruct Hrun as [[inside Hcall] | (a & inside & sp & Hat)];
    [| exfalso; exact (function_not_atomic C Hat eq_refl Hr Hwritten)].
  (* of each event the function makes itself: a call of code comes after no remove, and at a remove every call
     of code before it has been responded to *)
  assert (forall j, direct c i (history j) ->
    (forall code, itselfMakes history (Invocation_mk L.Function0_apply [code]) c i j ->
      forall s x k, k < j -> itselfMakes history (Invocation_mk
        L.KeySetView_remove [s; x]) c i k ->
      False) /\
    (forall s x, itselfMakes history (Invocation_mk
        L.KeySetView_remove [s; x]) c i j ->
      forall code w, w < j ->
        history w = Event_Invoke c (Some i) (Invocation_mk L.Function0_apply [code]) ->
        overBy history c w j)) as Hall.
  { refine (function_meets _ C Hcall eq_refl Hr Hwritten _).
    intros args' j' Hargs' _. apply vals_none in Hargs' as ->.
    (* it calls the code it was made to run, and is responded to *)
    step. intros wt mt yt yst Hwt Hp0 Hmt _ _ Hinv. typed_all. split; [miss |].
    intros wback rback spback xback Hwback Hresp _.
    (* whatever that gave: the herd's set is read, and `Thread.currentThread()` called *)
    pass. all: pass.
    (* it threw: so does the function; it returned: remove is called, and nothing of the two after *)
    all: step; [miss |]; intros wr ysr Hwr Hp Hysr Hrm; (split; [| intros; pass; pass]).
    all: split; [miss |]; intros s' x' _ code' w' Hw' Hinv'.
    all: pose proof (Hp w' Hw' ltac:(rewrite Hinv'; cbn; auto)) as Hin; cbn [In] in Hin.
    all: repeat (destruct Hin as [<- | Hin]); try contradiction;
      first [exists wback, rback, spback; split; [lia | exact Hresp] | revert Hinv'; miss]. }
  destruct (Hall w (makes_direct Hcode)) as [HA _]. destruct (Hall k (makes_direct Hrem)) as [_ HB].
  assert (w < k) as Hwk.
  { destruct (Z_lt_le_dec w k) as [Hlt | Hge]; [exact Hlt | exfalso]. destruct (Z.eq_dec w k) as [-> | Hdiff].
    - pose proof (makes_one Hcode Hrem) as Esame. discriminate Esame.
    - exact (HA code Hcode _ x k ltac:(lia) Hrem). }
  split; [exact Hwk |]. intros (_ & [ins Hbegun] & Hnotover). apply Hnotover. apply (HB _ x Hrem code w Hwk).
  destruct Hcode as [Eat | (? & ? & Eat)]; [exact Eat | rewrite Eat in Hbegun; discriminate Hbegun].
Qed.
