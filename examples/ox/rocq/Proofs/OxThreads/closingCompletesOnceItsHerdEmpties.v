Require Export FrFlowGen.OxThreads.closingCompletesOnceItsHerdEmpties.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.

(** Proven of `ThreadHerd.interruptAllAndJoinUntilCompleted`'s tree. Given its turn, the call checks its caller,
    sets the flag and loops; each call it makes is responded to. Once the flag is set adding stops, so each
    traversal is responded to. A turn of the loop asks the set whether it is empty: on a yes the call ends; on a
    no it traverses the set twice and comes to the next turn. Until adding ends there are finitely many moments,
    so finitely many turns; a turn after that traverses the set with no call adding to it, and so the set comes to
    rest empty, from some moment; until then there are finitely many turns again; and a turn after it is answered
    yes. *)
Lemma closingCompletesOnceItsHerdEmpties_Proofs_complete : closingCompletesOnceItsHerdEmpties_Obl_complete.
Proof.
  intros heldIn history elements flag [N C] Htraversals Hstops Hends Hcheck Hsetresp Hemptyresp Hfinds Hproceeds Hatomic
    Hconstructed Hmade Hfields h from [Hcalled Hempties].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit") C
    (Hmade h from ltac:(unfold calledOn; eauto 14)) eq_refl Hcalled) as (r0 & inside & Hh & Hcall).
  split; [exists inside; exact Hcall |].
  assert (moves history (heldIn L.ThreadHerd_herdOwner h) from) as Hmoves.
  { apply proceeds_moves. apply (Hproceeds h _ from). do 4 left. right. exists inside. exact Hcall. }
  assert (calledOn history h L.ThreadHerd_interruptAllAndJoinUntilCompleted from) as Hon
    by (unfold calledOn; eauto 14).
  pose proof (Hconstructed h from ltac:(do 4 left; right; exact Hon)) as Hcons.
  refine (method_leads _ C (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit")
    Hcall Hh eq_refl Hmoves _).
  intros args Hargs Hpassed. apply vals_none in Hargs as ->.
  (* the owner check is responded to *)
  lstep. intros w1 ys1 Hw1 Hq1 Hys1 Hinv1. apply args_one in Hys1 as (y0 & -> & Hy0).
  pose proof (one_name N _ _ _ Hy0 Hh) as ->.
  split.
  { destruct (Hcheck h _ w1 (conj (ex_intro _ _ Hinv1) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros w1d r1 sp1 x1 Hw1d Hq1d He1 Hg1 Hret1.
  leads_head.
  { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
  (* the flag is read, and set: setting is responded to *)
  lstep_rule. intros wf vfl yfl Hwf Hqf Hyfl Htyfl Hreadfl. apply (proj2 (proj1 (Hfields h))) in Hreadfl. subst yfl.
  lstep. intros ws yss Hws Hqs Hyss Hmks. apply args_two in Hyss as (ysA & ysB & -> & HysA & HysB).
  rewrite (one_name N _ _ _ HysA Hyfl) in *. apply named_bool in HysB. subst ysB.
  split.
  { intros Hinvs. destruct (Hsetresp _ _ _ ws (conj (ex_intro _ _ Hinvs) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wsd rs xs Hwsd Hqsd Hdones Hgs Hrets.
  leads_head.
  { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
  (* the flag is set from a moment on: so adding stops *)
  destruct rs as [yr | yr]; [| destruct Hgs].
  destruct (Hatomic _ True ws yr wsd (done_by_someone Hdones)) as (ms & [Hms1 Hms2] & Hflag).
  assert (flag (heldIn L.ThreadHerd_shutdownInProgress h) (ms + 1)) as Hset by (rewrite Hflag; exact I).
  pose proof (Hstops h (ms + 1) (conj (herd_constructed_later history h from (ms + 1) ltac:(lia) Hcons) Hset))
    as Hadding.
  pose proof (Hends h (ms + 1) (conj (herd_constructed_later history h from (ms + 1) ltac:(lia) Hcons) Hset))
    as Hending.
  (* its two variables are made *)
  lstep_rule. intros wv1 xv1 Hwv1 Hqv1 Hopv1.
  lstep. intros wv2 xv2 Hwv2 Hqv2 Hopv2.
  leads_head.
  (* a turn of the loop: it ends the call, or comes to the next turn, having asked and traversed *)
  lazymatch goal with |- leads ?T ?Cl ?Nn ?hh ?aa ?ii ?GG _ (Running (Iter B tt K)) =>
    assert (forall w, from < w ->
      (forall w' we rr wf f1 wt1 r1 wu1, w <= we -> we < wt1 -> wt1 < w' ->
         completedBy history
           (Invocation_mk L.CollectionView_isEmpty
             [heldIn L.ThreadHerd_threads h]) aa we rr wf ->
         rr <> Response_Returned (Value_Bool_ True) ->
         itselfMakes history
           (Invocation_mk
             L.KeySetView_forEach
             [heldIn L.ThreadHerd_threads h; f1]) aa from wt1 ->
         completedBy history
           (Invocation_mk
             L.KeySetView_forEach
             [heldIn L.ThreadHerd_threads h; f1]) aa wt1 r1 wu1 ->
         leads T Cl Nn hh aa ii GG w' (Running (Iter B tt K))) ->
      leads T Cl Nn hh aa ii GG w (Running (Iter B tt K))) as Hturn end.
  { intros w Hw Hnext. apply leads_iter.
    (* the set is read, and asked whether it is empty: asking is responded to *)
    lstep. intros wr vset yset Hwr Hqr Hyset Htyset Hread. apply (proj2 (Hfields h)) in Hread. subst yset.
    lstep. intros we yse Hwe Hqe Hyse Hmke. apply args_one in Hyse as (y3 & -> & Hy3).
    pose proof (one_name N _ _ _ Hy3 Hyset) as ->.
    split.
    { intros Hinve. destruct (Hemptyresp _ _ we (conj (ex_intro _ _ Hinve) I)) as (to & Hover).
      exact (over_responded _ _ from _ _ Hover). }
    intros wq rr xe Hwq Hqq Hask Hgivese Htye.
    leads_head.
      { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
    { (* yes: what interrupted closing is read, and the call ends *)
      lstep_rule. intros wx vx yx Hwx Hqx Hyx Htyx Hreadx.
      leads_head.
      1, 2: lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]).
      lstep_rule. intros wx2 vx2 yx2 Hwx2 Hqx2 Hyx2 Htyx2 Hreadx2.
      leads_head.
      all: lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
      (* no: the set is traversed twice, each traversal responded to, nothing more being added; then the next turn *)
    assert (rr <> Response_Returned (Value_Bool_ True)) as Hno.
    { intros ->. apply bool_named in Hgivese. destruct Hgivese as [Ht _]. discriminate (Ht I). }
    lstep_rule. intros wr1 vset1 yset1 Hwr1 Hqr1 Hyset1 Htyset1 Hread1. apply (proj2 (Hfields h)) in Hread1.
    subst yset1.
    lstep. intros wt1 yst1 Hwt1 Hqt1 Hyst1 Hmkt1. apply args_two in Hyst1 as (ya1 & yf1 & -> & Hya1 & _).
    pose proof (one_name N _ _ _ Hya1 Hyset1) as ->.
    split.
    { intros Hinvt.
      destruct (Htraversals h yf1 from wt1 (conj (conj Hcalled (or_introl Hinvt)) Hadding)) as [_ (to & Hover)].
      exact (over_responded _ _ from _ _ Hover). }
    intros wu1 rt1 xt1 Hwu1 Hqu1 Htrav1 Hgt1 Hrett1.
    leads_head.
    { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
    lstep_rule. intros wr2 vset2 yset2 Hwr2 Hqr2 Hyset2 Htyset2 Hread2. apply (proj2 (Hfields h)) in Hread2.
    subst yset2.
    lstep. intros wt2 yst2 Hwt2 Hqt2 Hyst2 Hmkt2. apply args_two in Hyst2 as (ya2 & yf2 & -> & Hya2 & _).
    pose proof (one_name N _ _ _ Hya2 Hyset2) as ->.
    split.
    { intros Hinvt.
      destruct (Htraversals h yf2 from wt2 (conj (conj Hcalled (or_introl Hinvt)) Hadding)) as [_ (to & Hover)].
      exact (over_responded _ _ from _ _ Hover). }
    intros wu2 rt2 xt2 Hwu2 Hqu2 Htrav2 Hgt2 Hrett2.
    leads_head.
    { lstep_rule; intros wZ rZ HwZ HqZ HeZ HgZ; exists (wZ + 1), wZ, rZ, []; (split; [lia | exact HeZ]). }
    eapply Hnext with (we := we) (wt1 := wt1);
      [lia | lia | lia | exact (done_completed Hask) | exact Hno | exact (done_made Htrav1)
      | exact (done_completed Htrav1)]. }
  (* once the set rests empty, a turn that asks is answered yes: the loop ends within the moments left *)
  lazymatch goal with |- leads ?T ?Cl ?Nn ?hh ?aa ?ii ?GG _ (Running (Iter B tt K)) =>
    assert (forall E0 E n w,
      E0 <= E -> emptyFrom elements history (heldIn L.ThreadHerd_threads h) E0 E ->
      from < w -> E - w < Z.of_nat n -> leads T Cl Nn hh aa ii GG w (Running (Iter B tt K))) as Hrested end.
  { intros E0 E n. induction n as [| n IH]; intros w H0E HE Hw Hn; apply Hturn; try exact Hw.
    all: intros wN weN rrN wqN fN wtN rN wuN Hwe Hwt1 HwN Hasked Hno Hmk1 Hdone1.
    all: destruct (Z_le_gt_dec E weN) as [Hle | Hgt];
      [exfalso; apply Hno;
        exact (Hfinds _ E0 E (conj H0E HE) weN rrN wqN
          (ex_intro (fun who => completedBy history _ who weN rrN wqN) _ Hasked) Hle) |].
    - lia.
    - apply IH; [exact H0E | exact HE | lia | lia]. }
  (* until adding ends there are finitely many moments; a traversal made after is followed by the set at rest *)
  lazymatch goal with |- leads ?T ?Cl ?Nn ?hh ?aa ?ii ?GG _ (Running (Iter B tt K)) =>
    assert (forall L n w,
      (forall y w0, L <= w0 -> ~ ((exists who, calledBy history
        (Invocation_mk L.KeySetView_add
          [heldIn L.ThreadHerd_threads h; y]) who w0) \/
        (exists m, m < w0 /\ exists who, begun history
          (Invocation_mk L.KeySetView_add
            [heldIn L.ThreadHerd_threads h; y]) who m /\ ~ overBy history who m w0))) ->
      from < w -> L - w < Z.of_nat n -> leads T Cl Nn hh aa ii GG w (Running (Iter B tt K))) as Hstopped end.
  { intros L n. induction n as [| n IH]; intros w HL Hw Hn; apply Hturn; try exact Hw.
    all: intros wN weN rrN wqN fN wtN rN wuN Hwe Hwt1 HwN Hasked Hno Hmk1 Hdone1.
    all: destruct (Z_le_gt_dec L wtN) as [Hle | Hgt].
    1, 3: assert (forall y w0, wtN <= w0 -> ~ ((exists who, calledBy history
        (Invocation_mk L.KeySetView_add
          [heldIn L.ThreadHerd_threads h; y]) who w0) \/
        (exists m, m < w0 /\ exists who, begun history
          (Invocation_mk L.KeySetView_add
            [heldIn L.ThreadHerd_threads h; y]) who m /\ ~ overBy history who m w0)))
        as HLt by (intros y w0 Hw0; apply HL; lia);
      destruct (Hempties fN from wtN rN wuN (conj (conj (conj Hcalled Hmk1) Hdone1) HLt)) as (E0 & E & H0E & HE);
      apply (Hrested E0 E (Z.to_nat (E - wN + 1)) wN H0E HE); lia.
    - lia.
    - apply IH; [exact HL | lia | lia]. }
  destruct Hending as [L HL]. apply (Hstopped L (Z.to_nat (L - wv2 + 1))); [exact HL | lia | lia].
Qed.

(** What it is from can hold: an execution in which nothing happens, of flags never set, meets each. *)
