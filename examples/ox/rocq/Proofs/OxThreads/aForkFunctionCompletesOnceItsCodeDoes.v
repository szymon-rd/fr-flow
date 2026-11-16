Require Export FrFlowGen.OxThreads.aForkFunctionCompletesOnceItsCodeDoes.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic FrFlow.Code.Live.

(** Proven of `ThreadHerd.startThread`'s tree, twice over. The function it hands the factory is the one written
    there, `try t finally threads.remove(Thread.currentThread()).discard`. Run by a thread that is given its
    turn, it calls the code startThread was given; once that is responded to, whatever it gave, it reads the
    set, asks for the current thread, removes it and discards the answer, each responded to in time; and it
    ends. *)
Lemma aForkFunctionCompletesOnceItsCodeDoes_Proofs_complete : aForkFunctionCompletesOnceItsCodeDoes_Obl_complete.
Proof.
  intros history [N C] Hproceeds Hcurrent Hremoving Hdiscard Hmade h r code t i [[Hfork Hrun] Hcode].
  pose proof Hfork as (c0 & from0 & f0 & m & Hstart & Hhand).
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h from0 ltac:(unfold calledOn; eauto 14)) eq_refl Hstart) as (r0 & inside0 & Hh & Hcall0).
  pose proof (Hproceeds h r code Hfork t i) as Hgoes. clear Hfork Hproceeds.
  revert t i Hrun Hcode Hgoes.
  refine (method_meets
    (fun j => forall f r, itselfMakes history (Invocation_mk
      "java.util.concurrent.ThreadFactory newThread java.lang.Runnable:java.lang.Thread" [f; r]) c0 from0 j ->
      forall t i, calledBy history (Invocation_mk "java.lang.Runnable run :scala.Unit" [r]) t i ->
      (forall m, itselfMakes history (Invocation_mk "scala.Function0 apply :java.lang.Object" [code]) t i m ->
        begun history (Invocation_mk "scala.Function0 apply :java.lang.Object" [code]) t m /\
        exists to, overBy history t m to) ->
      (forall w, (((i < w /\ begun history (Invocation_mk "java.lang.Runnable run :scala.Unit" [r]) t i) /\ True) /\
        ~ overBy history t i w) /\ ~ waitsForACall history t i w ->
        exists later, w <= later /\ actsItself history t i later) ->
      begun history (Invocation_mk "java.lang.Runnable run :scala.Unit" [r]) t i /\ exists to, overBy history t i to)
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall0 Hh eq_refl _ m
    (makes_direct Hhand) _ r Hhand).
  intros args j Hargs Hpassed. apply vals_one in Hargs as (vcode & -> & Hnamed).
  (* what startThread is given by name is a function *)
  inversion Hpassed as [| p v ps vs Hp _]; subst. lazy in Hp. destruct Hp as (body & sc0 & ->).
  (* the two checks; the factory is read *)
  pass. pass. pass.
  (* and handed a function: the one written here; what follows hands over none *)
  step. intros wn ysn _ _ Hysn Hmk. split; [| intros; pass; pass; pass; pass].
  intros f r' Hit t i Hrun Hcode Hgoes. pose proof (makes_one Hmk Hit) as E. injection E as ->.
  apply args_two in Hysn as (yf & yr & E & _ & Hr). injection E as <- <-.
  (* a thread runs it *)
  lazymatch type of Hr with names _ _ (VCode ?fn) =>
    assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  destruct Hrun as [[inside Hcall] | (a & inside & sp & Hat)];
    [| exfalso; exact (function_not_atomic C Hat eq_refl Hr Hwritten)].
  split; [exists inside; exact Hcall |].
  assert (moves history t i) as Hmoves.
  { apply proceeds_moves. intros w Hw Hnover Hnwaits. apply Hgoes.
    split; [split; [split; [split; [exact Hw | exists inside; exact Hcall] | exact I] | exact Hnover] |
      exact Hnwaits]. }
  refine (function_leads _ C Hcall eq_refl Hr Hwritten Hmoves _).
  intros args' Hargs' _. apply vals_none in Hargs' as ->.
  (* it calls the code it was made to run, which is responded to *)
  lstep. intros wt mt yt yst Hwt Hqt Hmt Hyt Hyst Hinv. typed_all. cbn in Hyst. apply args_none in Hyst as ->.
  pose proof (one_name N _ _ _ Hyt Hnamed) as ->.
  split.
  { destruct (Hcode wt (or_introl Hinv)) as [_ [to Hover]]. exact (over_responded _ _ i _ _ Hover). }
  intros wback rback spback xback Hwback Hqback Hresp Hgives.
  (* whatever that gave: the herd's set is read *)
  lstep.
  all: intros wth vth yth Hwth Hqth Hyth Htyth Hread.
  (* the current thread is asked for *)
  all: lstep; intros wc ysc Hwc Hqc Hysc Hmkc; apply args_none in Hysc as ->.
  all: (split; [intros Hinvc; destruct (Hcurrent t wc (conj (ex_intro _ _ Hinvc) I)) as (to & Hover);
    exact (over_responded _ _ i _ _ Hover) |]).
  all: intros wcd rc xc Hwcd Hqcd Hdonec Hgivesc Hretc.
  all: leads_head.
  (* that threw, and the function ends with it; or the thread is removed from the set *)
  all: try (lstep_rule; intros w9 r9 Hw9 Hq9 He9 Hg9; exists (w9 + 1), w9, r9, []; (split; [lia | exact He9])).
  all: lstep_rule; intros wr ysr Hwr Hqr Hysr Hmkr; apply args_two in Hysr as (ys1 & ys2 & -> & Hys1 & Hys2).
  all: (split; [intros Hinvr; destruct (Hremoving ys1 ys2 t wr (conj (ex_intro _ _ Hinvr) I)) as (to & Hover);
    exact (over_responded _ _ i _ _ Hover) |]).
  all: intros wrd rr xr Hwrd Hqrd Hdoner Hgivesr Hretr.
  all: leads_head.
  all: try (lstep_rule; intros w9 r9 Hw9 Hq9 He9 Hg9; exists (w9 + 1), w9, r9, []; (split; [lia | exact He9])).
  (* and the answer discarded *)
  all: lstep_rule; intros wd ysd Hwd Hqd Hysd Hmkd; apply args_one in Hysd as (yd & -> & Hyd).
  all: (split; [intros Hinvd; destruct (Hdiscard yd t wd (conj (ex_intro _ _ Hinvd) I)) as (to & Hover);
    exact (over_responded _ _ i _ _ Hover) |]).
  all: intros wdd rd xd Hwdd Hqdd Hdoned Hgivesd Hretd.
  all: leads_head.
  all: lstep_rule; intros w9 r9 Hw9 Hq9 He9 Hg9; exists (w9 + 1), w9, r9, []; (split; [lia | exact He9]).
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma aForkFunctionCompletesOnceItsCodeDoes_Proofs_feasible : aForkFunctionCompletesOnceItsCodeDoes_Obl_feasible.
Proof.
  exists (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h r code _ who from w [[[[_ H] _] _] _]. destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros who from [H _]. destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros s x who from [H _]. destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros x who from [H _]. destruct (nothing_begun_at_rest _ _ _ H). }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
