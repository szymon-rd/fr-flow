(** What a call does in time, one rule for each thing its program does next.

    `Logic` says what holds at each event a call makes; nothing there says the call makes one. That takes what
    moves it: a call that is pending and waits for no call it made makes an event of its own in time (`moves`),
    which a model states of the calls it is about, as an assumption. And of each call the program makes, that
    it is responded to in time: an assumption about what is outside the code, or what is proven of the code.

    `leads G w0 st`: the call, at the stage `st` at the moment `w0`, pending and waiting for nothing but what
    its stage says, comes to `G`. Rules:

    - `leads_done`: `G` holds already;
    - `leads_ret`: the program has its result, and the call responds with it in time;
    - `leads_read`, `leads_op`: a field read, an object made, a field written, in time;
    - `leads_called`: a call of what is outside the code is made in time, and once it is responded to;
    - `leads_method`, `leads_function`: the same of a method of the code, of a function;
    - `leads_iter`: a loop is its body, then the loop again or what follows it;
    - `leads_called_done`, `leads_method_done`: the call made is what was to come.

    A call known to make an event later (`ahead_…`) is responded to in each call it makes before it.

    `method_leads`, `module_leads` and `function_leads` say it of a call in an execution of the code. The
    tactic `lstep` applies the rule of what the program does next. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia Classical.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Code.Walk FrFlow.Code.Logic.
Require FrFlow.Scala.Jdk.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Set Implicit Arguments.

Section Live.

  Variable files : list tree.
  Variable T : table.
  Variable known : classes.
  Variable N : naming.
  Variable history : Z -> Event.

  (** The call: made at `i` by `a`. And what it is to come to. *)
  Variable a : Value.
  Variable i : Z.
  Variable G : Prop.

  Abbreviation takes := (takes T known N a i).
  Abbreviation quiet := (quiet history a i).

  (** The call is pending at `w0`: not responded to before. *)
  Definition pending (w0 : Z) : Prop := forall k r sp, k < w0 -> history k <> Event_Respond a i r sp.

  (** Each call the call itself made before `w0`, but the one made at `but`, was responded to before `w0`. *)
  Definition answered (but : option Z) (w0 : Z) : Prop :=
    forall m inner, m < w0 -> Some m <> but -> history m = Event_Invoke a (Some i) inner ->
      exists k r sp, k < w0 /\ history k = Event_Respond a m r sp.

  (** The call a stage waits for. *)
  Definition awaited (st : stage) : option Z :=
    match st with Waiting called _ _ => Some called | _ => None end.

  (** What moves the call: pending and waiting for no call it made, it makes an event of its own in time. *)
  Definition moves : Prop :=
    forall w, i < w -> pending w -> answered None w -> exists w', w <= w' /\ direct a i (history w').

  (** From `w0` on the call is at the stages `at_` says: an event of its own takes it to the next, and any
      other leaves it where it is. *)
  Definition staged (at_ : Z -> stage) (w0 : Z) : Prop :=
    forall w, w0 <= w ->
      (its (at_ w) a i (history w) -> takes w (history w) (at_ w) (at_ (w + 1))) /\
      (~ its (at_ w) a i (history w) -> at_ (w + 1) = at_ w).

  Definition leads (w0 : Z) (st : stage) : Prop :=
    moves -> i < w0 -> pending w0 -> answered (awaited st) w0 ->
    forall at_, at_ w0 = st -> staged at_ w0 -> G.

  Lemma leads_done w0 st : G -> leads w0 st.
  Proof. intros H _ _ _ _ _ _ _. exact H. Qed.

  (** ** The next event of a running call *)

  Lemma first_direct w0 w' :
    w0 <= w' -> direct a i (history w') -> exists w1, w0 <= w1 /\ direct a i (history w1) /\ quiet w0 w1.
  Proof.
    intros Hle Hd. remember (Z.to_nat (w' - w0)) as n eqn:En. revert w0 Hle En.
    induction n as [| n IH]; intros w0 Hle En.
    - exists w0. replace w0 with w' by lia. split; [lia | split; [exact Hd | intros v Hv; lia]].
    - destruct (classic (direct a i (history w0))) as [H0 | H0].
      + exists w0. split; [lia | split; [exact H0 | intros v Hv; lia]].
      + destruct (IH (w0 + 1) ltac:(lia) ltac:(lia)) as (w1 & Hw1 & Hd1 & Hq).
        exists w1. split; [lia | split; [exact Hd1 |]]. intros v Hv Hdv.
        destruct (Z.eq_dec v w0) as [-> | Hne]; [exact (H0 Hdv) | exact (Hq v ltac:(lia) Hdv)].
  Qed.

  Lemma staged_later at_ w0 w1 : staged at_ w0 -> w0 <= w1 -> staged at_ w1.
  Proof. intros H Hle w Hw. apply H. lia. Qed.

  Lemma stays_running at_ w0 p w1 :
    staged at_ w0 -> at_ w0 = Running p -> w0 <= w1 -> quiet w0 w1 -> at_ w1 = Running p.
  Proof.
    intros Hst H0 Hle Hq. remember (Z.to_nat (w1 - w0)) as n eqn:En. revert w1 Hle Hq En.
    induction n as [| n IH]; intros w1 Hle Hq En.
    - replace w1 with w0 by lia. exact H0.
    - assert (at_ (w1 - 1) = Running p) as Hprev by (apply IH; [lia | intros v Hv; apply Hq; lia | lia]).
      replace w1 with (w1 - 1 + 1) by lia. rewrite (proj2 (Hst (w1 - 1) ltac:(lia))); [exact Hprev |].
      rewrite Hprev. intros [Hd | []]. exact (Hq (w1 - 1) ltac:(lia) Hd).
  Qed.

  (** A running call makes its next event in time: what the rest of the walk is given of it. *)
  Lemma leads_running w0 p :
    (forall w1 st1 at_, w0 <= w1 -> i < w1 -> quiet w0 w1 -> takes w1 (history w1) (Running p) st1 ->
       moves -> pending w1 -> answered None w1 -> at_ (w1 + 1) = st1 -> staged at_ (w1 + 1) -> G) ->
    leads w0 (Running p).
  Proof.
    intros H Hm Hi Hp Ha at_ H0 Hst.
    destruct (Hm w0 Hi Hp Ha) as (w' & Hw' & Hd).
    destruct (first_direct Hw' Hd) as (w1 & Hw1 & Hd1 & Hq).
    pose proof (stays_running Hst H0 Hw1 Hq) as Hat.
    pose proof (proj1 (Hst w1 Hw1) ltac:(rewrite Hat; left; exact Hd1)) as Ht. rewrite Hat in Ht.
    refine (H w1 (at_ (w1 + 1)) at_ Hw1 ltac:(lia) Hq Ht Hm _ _ eq_refl (staged_later (w1 := w1 + 1) Hst ltac:(lia))).
    - intros k r sp Hk E. destruct (Z_lt_le_dec k w0) as [Hlt | Hge]; [exact (Hp k r sp Hlt E) |].
      apply (Hq k ltac:(lia)). rewrite E. cbn. auto.
    - intros m inner Hlt _ E. destruct (Z_lt_le_dec m w0) as [Hlt0 | Hge].
      + destruct (Ha m inner Hlt0 ltac:(discriminate) E) as (k & r & sp & Hk & Ek).
        exists k, r, sp. split; [lia | exact Ek].
      + exfalso. apply (Hq m ltac:(lia)). rewrite E. cbn. auto.
  Qed.

  (** After an event that is neither a response to the call nor a call it makes to be responded to later, the
      call is pending and waits for nothing, as before it. *)
  Lemma pending_on w1 : pending w1 -> (forall r sp, history w1 <> Event_Respond a i r sp) -> pending (w1 + 1).
  Proof.
    intros Hp Hn k r sp Hk E. destruct (Z.eq_dec k w1) as [-> | Hne]; [exact (Hn r sp E) |].
    exact (Hp k r sp ltac:(lia) E).
  Qed.

  Lemma answered_on w1 :
    answered None w1 -> (forall inside inner, history w1 <> Event_Invoke a inside inner) -> answered None (w1 + 1).
  Proof.
    intros Ha Hn m inner Hm _ E. destruct (Z.eq_dec m w1) as [-> | Hne]; [destruct (Hn _ _ E) |].
    destruct (Ha m inner ltac:(lia) ltac:(discriminate) E) as (k & r & sp & Hk & Ek).
    exists k, r, sp. split; [lia | exact Ek].
  Qed.

  (** ** The rules *)

  (** The program has its result: the call responds with it, in time. *)
  Lemma leads_ret w0 (x : res) :
    (forall w1 r, w0 <= w1 -> quiet w0 w1 -> history w1 = Event_Respond a i r [] -> gives N r x -> G) ->
    leads w0 (Running (Ret x)).
  Proof.
    intros H. apply leads_running. intros w1 st1 at_ Hw1 _ Hq Ht _ _ _ _ _.
    apply takes_ret in Ht as (r & He & Hg & _). exact (H w1 r Hw1 Hq He Hg).
  Qed.

  Lemma op_event_kind X (o : Machine.op code obj X) x e :
    op_event T known N a i o x e ->
    (forall r sp, e <> Event_Respond a i r sp) /\ (forall inside inner, e <> Event_Invoke a inside inner).
  Proof.
    destruct o; cbn [op_event]; intros H; try contradiction.
    all: repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end.
    all: try (subst e; split; intros; discriminate).
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; split; intros; discriminate.
  Qed.

  (** An operation on an object of the code, in time. *)
  Lemma leads_op w0 X (o : Machine.op code obj X) (k : X -> program) :
    ~ outside_call o -> ~ unsaid o ->
    (forall w1 x, w0 <= w1 -> quiet w0 w1 -> op_event T known N a i o x (history w1) ->
       leads (w1 + 1) (Running (k x))) ->
    leads w0 (Running (Vis o k)).
  Proof.
    intros Hext Hsaid H. apply leads_running. intros w1 st1 at_ Hw1 Hi1 Hq Ht Hm Hp Ha Hat Hst.
    apply (takes_op_of Hext Hsaid) in Ht as (x & Hop & ->).
    destruct (op_event_kind _ _ _ Hop) as [Hnr Hni].
    exact (H w1 x Hw1 Hq Hop Hm ltac:(lia) (pending_on Hp Hnr) (answered_on Ha Hni) at_ Hat Hst).
  Qed.

  (** A field of an object is read, in time: the value read is of the field's type. *)
  Lemma leads_read w0 yh cls r f (k : exn + val -> program) :
    names N yh (vref cls r) ->
    (forall w1 v y, w0 <= w1 -> quiet w0 w1 -> names N y v -> field_typed T known cls f v ->
       history w1 = Event_Read a (Some i) yh (field_label T cls f) y -> leads (w1 + 1) (Running (k (inr v)))) ->
    leads w0 (Running (Vis (ObjGet r f) k)).
  Proof.
    intros Hyh H. apply leads_running. intros w1 st1 at_ Hw1 Hi1 Hq Ht Hm Hp Ha Hat Hst.
    apply takes_read in Ht as (v & y & yo & Hyo & Hy & Hty & He & ->).
    destruct (read_place Hyh Hyo) as [-> Hcls]. rewrite Hcls in Hty, He.
    refine (H w1 v y Hw1 Hq Hy Hty He Hm ltac:(lia) (pending_on Hp _) (answered_on Ha _) at_ Hat Hst).
    - intros r' sp E. rewrite He in E. discriminate E.
    - intros ins inner E. rewrite He in E. discriminate E.
  Qed.

  Hypothesis conformed : conforms files T known N history.

  (** A call that waits is where it is until the response it waits for, and makes no event of its own. *)
  Lemma waits_until at_ w1 called typed (k : res -> program) w2 r sp :
    staged at_ w1 -> at_ w1 = Waiting called typed k -> w1 <= w2 ->
    history w2 = Event_Respond a called r sp ->
    at_ w2 = Waiting called typed k /\ quiet w1 w2.
  Proof.
    intros Hst H1 Hle He. remember (Z.to_nat (w2 - w1)) as n eqn:En.
    assert (forall (m : nat) v, v = w1 + Z.of_nat m -> v <= w2 ->
      at_ v = Waiting called typed k /\ quiet w1 v) as Hall.
    { induction m as [| m IH]; intros v Ev Hv.
      - replace v with w1 by lia. split; [exact H1 | intros u Hu; lia].
      - destruct (IH (v - 1) ltac:(lia) ltac:(lia)) as [Hat Hq].
        assert (~ its (at_ (v - 1)) a i (history (v - 1))) as Hnot.
        { intros Hits. pose proof (proj1 (Hst (v - 1) ltac:(lia)) Hits) as Ht. rewrite Hat in Ht.
          apply takes_waiting in Ht as (r' & sp' & x & E & _).
          pose proof (responded_once conformed E He). lia. }
        split.
        + replace v with (v - 1 + 1) by lia. rewrite (proj2 (Hst (v - 1) ltac:(lia)) Hnot). exact Hat.
        + intros u Hu Hd. destruct (Z.eq_dec u (v - 1)) as [-> | Hne]; [apply Hnot; left; exact Hd |].
          exact (Hq u ltac:(lia) Hd). }
    exact (Hall (Z.to_nat (w2 - w1)) w2 ltac:(lia) ltac:(lia)).
  Qed.

  (** A call that waits and makes an event of its own later was responded to. *)
  Lemma answered_by_next at_ w1 typed (k : res -> program) w3 :
    staged at_ (w1 + 1) -> at_ (w1 + 1) = Waiting w1 typed k -> i < w1 -> w1 < w3 ->
    direct a i (history w3) -> exists w2 r sp, history w2 = Event_Respond a w1 r sp.
  Proof.
    intros Hst Hat Hi Hlt Hd. destruct (classic (exists w2 r sp, history w2 = Event_Respond a w1 r sp))
      as [Hyes | Hno]; [exact Hyes | exfalso].
    assert (forall (n : nat), at_ (w1 + 1 + Z.of_nat n) = Waiting w1 typed k) as Hall.
    { induction n as [| n IH].
      - replace (w1 + 1 + Z.of_nat 0) with (w1 + 1) by lia. exact Hat.
      - replace (w1 + 1 + Z.of_nat (S n)) with (w1 + 1 + Z.of_nat n + 1) by lia.
        rewrite (proj2 (Hst (w1 + 1 + Z.of_nat n) ltac:(lia))); [exact IH |].
        intros Hits. pose proof (proj1 (Hst (w1 + 1 + Z.of_nat n) ltac:(lia)) Hits) as Ht. rewrite IH in Ht.
        apply takes_waiting in Ht as (r & sp & x & E & _). apply Hno. eauto. }
    pose proof (Hall (Z.to_nat (w3 - (w1 + 1)))) as H3.
    replace (w1 + 1 + Z.of_nat (Z.to_nat (w3 - (w1 + 1)))) with w3 in H3 by lia.
    pose proof (proj1 (Hst w3 ltac:(lia))) as Ht. rewrite H3 in Ht.
    specialize (Ht (or_introl Hd)). apply takes_waiting in Ht as (r & sp & x & E & _). apply Hno. eauto.
  Qed.

  (** A call the call made at `w1` is responded to in time: it is shown to be, or the call is known to make
      an event of its own later. *)
  Definition responded (w1 : Z) : Prop :=
    (exists w2 r sp, history w2 = Event_Respond a w1 r sp) \/ (exists w3, w1 < w3 /\ direct a i (history w3)).

  (** A call the call made at `w1`, once it is responded to: the call goes on with what it was given. *)
  Lemma leads_answered w1 inner typed (k : res -> program) at_ :
    moves -> i < w1 -> pending w1 -> answered None w1 ->
    history w1 = Event_Invoke a (Some i) inner ->
    at_ (w1 + 1) = Waiting w1 typed k -> staged at_ (w1 + 1) ->
    responded w1 ->
    (forall w2 r sp x, w1 < w2 -> quiet (w1 + 1) w2 -> history w2 = Event_Respond a w1 r sp -> gives N r x ->
       typed x -> leads (w2 + 1) (Running (k x))) ->
    G.
  Proof.
    intros Hm Hi Hp Ha He Hat Hst Hresp H.
    assert (exists w2 r sp, history w2 = Event_Respond a w1 r sp) as (w2 & r & sp & He2).
    { destruct Hresp as [Hyes | (w3 & Hlt3 & Hd3)]; [exact Hyes |].
      exact (answered_by_next Hst Hat Hi Hlt3 Hd3). }
    pose proof (responded_after conformed He2) as Hlt.
    destruct (waits_until (w2 := w2) Hst Hat ltac:(lia) He2) as [Hat2 Hq].
    pose proof (proj1 (Hst w2 ltac:(lia))) as Ht. rewrite Hat2 in Ht.
    specialize (Ht ltac:(right; rewrite He2; cbn; auto)).
    apply takes_waiting in Ht as (r' & sp' & x & E & Hg & Hty & Hnext).
    rewrite He2 in E. injection E as <- <-.
    refine (H w2 r sp x Hlt Hq He2 Hg Hty Hm ltac:(lia) _ _ at_ Hnext
      (staged_later (w1 := w2 + 1) Hst ltac:(lia))).
    - intros k' r' sp' Hk E. destruct (Z.eq_dec k' w2) as [-> | Hn2].
      { rewrite He2 in E. injection E as E _ _. lia. }
      destruct (Z_lt_le_dec k' w1) as [Hl | Hg']; [exact (Hp k' r' sp' Hl E) |].
      destruct (Z.eq_dec k' w1) as [-> | Hn1]; [rewrite He in E; discriminate E |].
      apply (Hq k' ltac:(lia)). rewrite E. cbn. auto.
    - intros m inner' Hlm _ E. destruct (Z.eq_dec m w1) as [-> | Hn1].
      { exists w2, r, sp. split; [lia | exact He2]. }
      destruct (Z_lt_le_dec m w1) as [Hl | Hg'].
      { destruct (Ha m inner' Hl ltac:(discriminate) E) as (k' & r' & sp' & Hk & Ek).
        exists k', r', sp'. split; [lia | exact Ek]. }
      destruct (Z.eq_dec m w2) as [-> | Hn2]; [rewrite He2 in E; discriminate E |].
      exfalso. apply (Hq m ltac:(lia)). rewrite E. cbn. auto.
  Qed.

  (** A call of what is outside the code is made in time; it is responded to in time, which is to be shown of
      it; and then the call goes on with a result of the type its signature says. *)
  Lemma leads_called w0 m args (k : res -> program) :
    (forall w1 ys, w0 <= w1 -> quiet w0 w1 -> Forall2 (names N) ys args ->
       makes a i (history w1) (Invocation_mk m ys) ->
       (history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) -> responded w1) /\
       forall w2 r x, w1 < w2 -> quiet (w1 + 1) (w2 - 1) -> done_inside history a i m ys w1 r w2 ->
         gives N r x -> returns known m x -> leads w2 (Running (k x))) ->
    leads w0 (Running (Vis (ExtCall 0 m args) k)).
  Proof.
    intros H. apply leads_running. intros w1 st1 at_ Hw1 Hi1 Hq Ht Hm Hp Ha Hat Hst.
    apply takes_outside in Ht as (ys & Hys & [[He ->] | (r & sp & x & He & Hg & Hr & ->)]).
    - destruct (H w1 ys Hw1 Hq Hys (or_introl He)) as [Hresp Hk].
      refine (leads_answered Hm Hi1 Hp Ha He Hat Hst (Hresp He) _).
      intros w2 r sp x Hlt Hq2 He2 Hg Hty. apply (Hk (w2 + 1) r x); [lia | | | exact Hg | exact Hty].
      { replace (w2 + 1 - 1) with w2 by lia. exact Hq2. }
      right. replace (w2 + 1 - 1) with w2 by lia. split; [exact He | split; [lia | exists sp; exact He2]].
    - destruct (H w1 ys Hw1 Hq Hys (or_intror (ex_intro _ r (ex_intro _ sp He)))) as [_ Hk].
      refine (Hk (w1 + 1) r x ltac:(lia) _ _ Hg Hr Hm ltac:(lia) (pending_on Hp _) (answered_on Ha _) at_ Hat
        Hst).
      + intros v Hv. lia.
      + left. exists sp. split; [exact He | reflexivity].
      + intros r' sp' E. rewrite He in E. discriminate E.
      + intros ins inner E. rewrite He in E. discriminate E.
  Qed.

  (** A call of a method of the code is made in time; it is responded to in time, which is to be shown of it;
      and then the call goes on with what it gave, of the class its signature names. *)
  Lemma leads_method w0 s on args (k : res -> program) m :
    label_of s = m ->
    (forall w1 ys, w0 <= w1 -> quiet w0 w1 -> Forall2 (names N) ys (receiver on ++ args) ->
       history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) ->
       responded w1 /\
       forall w2 r sp x, w1 < w2 -> quiet (w1 + 1) w2 -> history w2 = Event_Respond a w1 r sp ->
         gives N r x -> returns known m x -> leads (w2 + 1) (Running (k x))) ->
    leads w0 (Running (Call (Method s) (VList (on :: args)) k)).
  Proof.
    intros <- H. apply leads_running. intros w1 st1 at_ Hw1 Hi1 Hq Ht Hm Hp Ha Hat Hst.
    apply takes_method_call in Ht as (ys & Hys & He & ->).
    destruct (H w1 ys Hw1 Hq Hys He) as [Hresp Hk].
    exact (leads_answered Hm Hi1 Hp Ha He Hat Hst Hresp Hk).
  Qed.

  (** A call of a function, the same. *)
  Lemma leads_function w0 c arg (k : res -> program) :
    applied c arg ->
    (forall w1 m y ys, w0 <= w1 -> quiet w0 w1 -> called_as c arg m -> names N y (VCode c) ->
       Forall2 (names N) ys (arguments arg) ->
       history w1 = Event_Invoke a (Some i) (Invocation_mk m (y :: ys)) ->
       responded w1 /\
       forall w2 r sp x, w1 < w2 -> quiet (w1 + 1) w2 -> history w2 = Event_Respond a w1 r sp ->
         gives N r x -> leads (w2 + 1) (Running (k x))) ->
    leads w0 (Running (Call c arg k)).
  Proof.
    intros Hc H. apply leads_running. intros w1 st1 at_ Hw1 Hi1 Hq Ht Hm Hp Ha Hat Hst.
    apply (takes_function_call Hc) in Ht as (m & y & ys & Hcm & Hy & Hys & He & ->).
    destruct (H w1 m y ys Hw1 Hq Hcm Hy Hys He) as [Hresp Hk].
    refine (leads_answered Hm Hi1 Hp Ha He Hat Hst Hresp _).
    intros w2 r sp x Hlt Hq2 He2 Hg _. exact (Hk w2 r sp x Hlt Hq2 He2 Hg).
  Qed.

  (** The call is made, and that is what was to come: nothing is asked of what follows. *)
  Lemma leads_called_done w0 m args (k : res -> program) :
    (forall w1 ys, w0 <= w1 -> quiet w0 w1 -> Forall2 (names N) ys args ->
       makes a i (history w1) (Invocation_mk m ys) -> G) ->
    leads w0 (Running (Vis (ExtCall 0 m args) k)).
  Proof.
    intros H. apply leads_running. intros w1 st1 at_ Hw1 Hi1 Hq Ht _ _ _ _ _.
    apply takes_outside in Ht as (ys & Hys & [[He _] | (r & sp & x & He & _)]).
    - exact (H w1 ys Hw1 Hq Hys (or_introl He)).
    - exact (H w1 ys Hw1 Hq Hys (or_intror (ex_intro _ r (ex_intro _ sp He)))).
  Qed.

  Lemma leads_method_done w0 s on args (k : res -> program) m :
    label_of s = m ->
    (forall w1 ys, w0 <= w1 -> quiet w0 w1 -> Forall2 (names N) ys (receiver on ++ args) ->
       history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) -> G) ->
    leads w0 (Running (Call (Method s) (VList (on :: args)) k)).
  Proof.
    intros <- H. apply leads_running. intros w1 st1 at_ Hw1 Hi1 Hq Ht _ _ _ _ _.
    apply takes_method_call in Ht as (ys & Hys & He & _). exact (H w1 ys Hw1 Hq Hys He).
  Qed.

  (** ** An event the call is known to make later

      A call that is known to make an event at `later` (it has been seen to add a thread, say) is responded to
      in each call it makes before: what the walk has not reached yet is still ahead of it. *)

  Lemma ahead_quiet w0 w1 later : quiet w0 w1 -> w0 <= later -> direct a i (history later) -> w1 <= later.
  Proof.
    intros Hq Hle Hd. destruct (Z_lt_le_dec later w1) as [Hlt | Hge]; [| exact Hge].
    destruct (Hq later ltac:(lia) Hd).
  Qed.

  Lemma ahead_other w0 w1 later :
    quiet w0 w1 -> w0 <= later -> direct a i (history later) -> later <> w1 -> w1 + 1 <= later.
  Proof. intros Hq Hle Hd Hne. pose proof (ahead_quiet Hq Hle Hd). lia. Qed.

  Lemma ahead_answered w1 w2 later inv r sp :
    makes a i (history later) inv -> w1 + 1 <= later -> quiet (w1 + 1) w2 ->
    history w2 = Event_Respond a w1 r sp -> w2 + 1 <= later.
  Proof.
    intros Hmk Hle Hq He. apply (ahead_other Hq Hle (makes_direct Hmk)). intros ->.
    destruct Hmk as [E | (? & ? & E)]; rewrite He in E; discriminate E.
  Qed.

  Lemma ahead_done w1 w2 later inv m ys r :
    makes a i (history later) inv -> w1 + 1 <= later -> quiet (w1 + 1) (w2 - 1) ->
    done_inside history a i m ys w1 r w2 -> w2 <= later.
  Proof.
    intros Hmk Hle Hq [(sp & _ & ->) | (_ & Hlt & sp & He)]; [exact Hle |].
    pose proof (ahead_other Hq Hle (makes_direct Hmk)) as H. apply Z.le_trans with (w2 - 1 + 1); [lia |].
    apply H. intros ->. destruct Hmk as [E | (? & ? & E)]; rewrite He in E; discriminate E.
  Qed.

  (** What the call does before an event it is known to make later is responded to. *)
  Lemma responded_ahead w1 later : w1 < later -> direct a i (history later) -> responded w1.
  Proof. intros Hlt Hd. right. exists later. split; assumption. Qed.

  (** ** Programs that take the same events *)

  (** A program that takes each event another takes comes to what the other comes to. *)
  Lemma leads_alike w0 p q :
    (forall v e st, takes v e (Running p) st -> takes v e (Running q) st) ->
    leads w0 (Running q) -> leads w0 (Running p).
  Proof.
    intros Hpq H Hm Hi Hp Ha at_ H0 Hst.
    destruct (Hm w0 Hi Hp Ha) as (w' & Hw' & Hd).
    destruct (first_direct Hw' Hd) as (w1 & Hw1 & Hd1 & Hq).
    pose proof (stays_running Hst H0 Hw1 Hq) as Hat.
    apply (H Hm Hi Hp Ha (fun w => if Z.leb w w1 then Running q else at_ w)).
    { rewrite (proj2 (Z.leb_le w0 w1) Hw1). reflexivity. }
    intros w Hw. destruct (Z_lt_le_dec w w1) as [Hlt | Hge].
    - rewrite (proj2 (Z.leb_le w w1) ltac:(lia)), (proj2 (Z.leb_le (w + 1) w1) ltac:(lia)).
      split; [| reflexivity]. intros [Hdw | []]. destruct (Hq w ltac:(lia) Hdw).
    - destruct (Z.eq_dec w w1) as [-> | Hne].
      + rewrite (proj2 (Z.leb_le w1 w1) ltac:(lia)), (proj2 (Z.leb_gt (w1 + 1) w1) ltac:(lia)).
        split; [| intros Hn; destruct Hn; left; exact Hd1]. intros _.
        apply Hpq. rewrite <- Hat. apply (proj1 (Hst w1 Hw1)). rewrite Hat. left. exact Hd1.
      + rewrite (proj2 (Z.leb_gt w w1) ltac:(lia)), (proj2 (Z.leb_gt (w + 1) w1) ltac:(lia)).
        exact (Hst w Hw).
  Qed.

  (** A loop is its body, and then the loop again or what follows it. *)
  Lemma leads_iter w0 S B (body : S -> Machine.P code obj (S + B)) s (k : B -> program) :
    leads w0 (Running (unfold_iter body s k)) -> leads w0 (Running (Iter body s k)).
  Proof. apply leads_alike. intros v e st. apply takes_iter. Qed.

  Lemma leads_made w0 cls arg (k : res -> program) :
    leads w0 (Running (pbind (run T (Init cls) arg) k)) -> leads w0 (Running (Call (Init cls) arg k)).
  Proof. apply leads_alike. intros v e st. apply takes_made. Qed.

  Lemma leads_stood w0 b sc (k : res -> program) :
    leads w0 (Running (pbind (run T (Thunk b sc) (VList [])) k)) ->
    leads w0 (Running (Call (Thunk b sc) (VList []) k)).
  Proof. apply leads_alike. intros v e st. apply takes_stood. Qed.

  (** ** A call in an execution of the code *)

  Lemma begins p :
    follows T known N history a i p ->
    pending (i + 1) /\ answered None (i + 1) /\
    exists at_, at_ (i + 1) = Running p /\ staged at_ (i + 1).
  Proof.
    intros (Hbefore & _ & at_ & H0 & H). split; [| split].
    - intros k r sp Hk E. pose proof (responded_after conformed E). lia.
    - intros m inner Hm _ E. exfalso. apply (Hbefore m ltac:(lia)). rewrite E. cbn. auto.
    - exists at_. split; [exact H0 |]. intros w Hw. apply H. lia.
  Qed.

  (** A call of a method of the code comes to `G`, if its program does and the call moves. *)
  Lemma method_leads inside s cls r d y ys :
    history i = Event_Invoke a inside (Invocation_mk (label_of s) (y :: ys)) ->
    names N y (vref cls r) -> impl T cls s = Some d -> moves ->
    (forall args, Forall2 (names N) ys args -> passed known d args ->
       leads (i + 1) (Running (run T (Method s) (VList (vref cls r :: args))))) ->
    G.
  Proof.
    intros He Hy Hd Hm H. destruct conformed as (Hcalls & _).
    destruct (Hcalls i a inside s cls r d y ys He Hy Hd) as (args & Hargs & Hp & Hf).
    destruct (begins Hf) as (Hpend & Hans & at_ & H0 & Hst).
    exact (H args Hargs Hp Hm ltac:(lia) Hpend Hans at_ H0 Hst).
  Qed.

  (** A call of a method of an object of the code that is alone of its class. *)
  Lemma module_leads inside owner name signature c d ys :
    history i = Event_Invoke a inside (Invocation_mk (label owner name signature) ys) ->
    class_of T owner = Some c -> is_module c = true -> impl T owner (Member owner name signature) = Some d ->
    moves ->
    (forall args, Forall2 (names N) ys args -> passed known d args ->
       leads (i + 1)
         (Running (run T (Method (Member owner name signature)) (VList (module_val T owner :: args))))) ->
    G.
  Proof.
    intros He Hc Hmod Hd Hm H. destruct conformed as (_ & Hcalls & _).
    destruct (Hcalls i a inside owner name signature c d ys He Hc Hmod Hd) as (args & Hargs & Hp & Hf).
    destruct (begins Hf) as (Hpend & Hans & at_ & H0 & Hst).
    exact (H args Hargs Hp Hm ltac:(lia) Hpend Hans at_ H0 Hst).
  Qed.

  (** A call of a function the code wrote. *)
  Lemma function_leads inside m c y ys :
    history i = Event_Invoke a inside (Invocation_mk m (y :: ys)) ->
    applies known m = true -> names N y (VCode c) -> written files c -> moves ->
    (forall args, Forall2 (names N) ys args -> given known c args -> leads (i + 1) (Running (run T c (VList args)))) ->
    G.
  Proof.
    intros He Hap Hy Hw Hm H. destruct conformed as (_ & _ & Hcalls & _).
    destruct (Hcalls i a inside m c y ys He Hap Hy Hw) as (args & Hargs & Hg & Hf).
    destruct (begins Hf) as (Hpend & Hans & at_ & H0 & Hst).
    exact (H args Hargs Hg Hm ltac:(lia) Hpend Hans at_ H0 Hst).
  Qed.

End Live.

Arguments method_leads {files T known N history a i} G conformed {inside} s {cls r d y ys} _ _ _ _ _.
Arguments module_leads {files T known N history a i} G conformed {inside} owner name signature {c d ys}
  _ _ _ _ _ _.
Arguments function_leads {files T known N history a i} G conformed {inside m c y ys} _ _ _ _ _ _.

(** ** Going through a program, to what it comes to *)

(** The program of the goal with its next step computed, as `meets_head` does. *)
Ltac leads_head :=
  typed_all;
  lazymatch goal with
  | |- leads ?T ?C ?N ?h ?a ?i ?G ?w0 (Running ?p) =>
      let p' :=
        eval lazy head beta iota zeta delta -[implemented held equal val_eqb Jdk.as_exn any some_of] in p in
      lazymatch p' with
      | Vis ?o ?k =>
          let o' := eval lazy beta iota zeta delta -[receiver val_eqb some_of] in o in
          let K := fresh "K" in
          pose (K := k); change (leads T C N h a i G w0 (Running (Vis o' K))); aside_clear;
          repeat match goal with E : receiver ?v = _ |- _ => rewrite E end; cbn [app]
      | Call (Init ?cls) ?arg ?k => apply leads_made; leads_head
      | Call (Thunk ?b ?sc) (VList []) ?k => apply leads_stood; leads_head
      | Call ?c ?arg ?k =>
          let c' := eval lazy beta iota zeta delta -[val_eqb some_of] in c in
          let arg' := eval lazy beta iota zeta delta -[val_eqb some_of] in arg in
          let K := fresh "K" in
          pose (K := k); change (leads T C N h a i G w0 (Running (Call c' arg' K))); aside_clear
      | Ret ?x =>
          let x' := eval lazy beta iota zeta delta -[val_eqb some_of] in x in
          change (leads T C N h a i G w0 (Running (Ret x'))); aside_clear
      | Iter ?body ?s ?k =>
          first
            [ is_var body; is_var k; change (leads T C N h a i G w0 (Running (Iter body s k)))
            | let B := fresh "B" in
              let K := fresh "K" in
              pose (B := body); pose (K := k); change (leads T C N h a i G w0 (Running (Iter B s K))) ];
          aside_clear
      | _ =>
          change (leads T C N h a i G w0 (Running p')); aside_clear;
          first [meets_answer; leads_head | meets_each p'; leads_head | idtac]
      end
  end.

(** The rule of what the program does next. *)
Ltac lstep_rule :=
  lazymatch goal with
  | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ObjGet _ _) _)) => eapply leads_read; [eassumption |]
  | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) => eapply leads_called; [eassumption |]
  | |- leads _ _ _ _ _ _ _ _ (Running (Vis _ _)) => apply leads_op; [intros [] | intros [] |]
  | |- leads _ _ _ _ _ _ _ _ (Running (Call (Method ?s) _ _)) =>
      let said := eval lazy in (label_of s) in
      eapply leads_method with (m := said); [eassumption | reflexivity |]
  | |- leads _ _ _ _ _ _ _ _ (Running (Call _ _ _)) => eapply leads_function; [eassumption | exact I |]
  | |- leads _ _ _ _ _ _ _ _ (Running (Ret _)) => apply leads_ret
  end.

Ltac lstep := leads_head; lstep_rule.

(** The rule of a call that is what was to come. *)
Ltac lstep_done :=
  leads_head;
  lazymatch goal with
  | |- leads _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) => apply leads_called_done
  | |- leads _ _ _ _ _ _ _ _ (Running (Call (Method ?s) _ _)) =>
      let said := eval lazy in (label_of s) in eapply leads_method_done with (m := said); [reflexivity |]
  end.
