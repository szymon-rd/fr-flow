(** Proving a claim of code from its execution: walking a call's program along the events it makes.

    `conforms` gives, for a call of the code, the stage it is at before each moment (`follows`). A proof takes
    the call from its start (`steps`), an event of its own at a time (`steps_next`): the program's next
    operation says what the event is (`takes_read`, `takes_outside`, …), and the proof goes on with what follows
    it. The program is never computed whole: `walk_head` computes what it does next. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Ascii Lia Classical_Prop ProofIrrelevanceFacts.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Equal FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Code.Outside FrFlow.Code.Conforms.
Require Export FrFlow.Code.Classes.
Import ListNotations.
Open Scope string_scope.

(** Two operations of one type that are the same are the same: from classical logic alone. *)
Module Irrelevance. Definition proof_irrelevance := Classical_Prop.proof_irrelevance. End Irrelevance.
Module Dependent := ProofIrrelevanceTheory Irrelevance.

(** ** The execution in which nothing happens is one of any code *)

Definition plain_val (x : Value) : option val :=
  match x with
  | Value_Unit_ => Some VUnit
  | Value_Bool_ P =>
      if excluded_middle_informative (P = (true = true)) then Some (VBool true)
      else if excluded_middle_informative (P = (false = true)) then Some (VBool false)
      else None
  | Value_Int_ z => Some (vint z)
  | Value_Str s => Some (vstr s)
  | Value_Reference _ => None
  end.

Lemma truths_differ : (false = true) <> (true = true).
Proof. intros H. assert (false = true) as F by (rewrite H; reflexivity). discriminate F. Qed.

Lemma plain_one (x y : Value) (v : val) : plain_val x = Some v -> plain_val y = Some v -> x = y.
Proof.
  destruct x as [| P | z | s | r], y as [| Q | z' | s' | r']; cbn; try congruence;
    repeat match goal with |- context [excluded_middle_informative ?A] => destruct (excluded_middle_informative A) end;
    try congruence; intros H1 H2; rewrite <- H2 in H1; try discriminate H1; injection H1; intros; congruence.
Qed.

Definition plain_naming : naming.
Proof.
  refine (Naming plain_val (fun _ => "") eq_refl _ (fun _ => eq_refl) (fun _ => eq_refl) plain_one _).
  - intros [|]; cbn.
    + destruct (excluded_middle_informative _) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
    + destruct (excluded_middle_informative _) as [e | _]; [exfalso; exact (truths_differ e) |].
      destruct (excluded_middle_informative _) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
  - intros [| P | z | s | r] c r'; cbn; try discriminate;
      repeat destruct (excluded_middle_informative _); discriminate.
Defined.

Lemma nothing_runs (files : list tree) (T : table) : runs files T (fun _ => Event_Stutter).
Proof.
  exists plain_naming. split; [| split; [| split]].
  - intros i a inside m ys p H. discriminate H.
  - intros w a inside m ys r spawns p H. discriminate H.
  - intros w b inside y cls hs H. discriminate H.
  - intros w w' b inside y cls hs b' inside' cls' hs' H. discriminate H.
Qed.

Set Implicit Arguments.

Section Walk.

  Variable files : list tree.
  Variable T : table.
  Variable N : naming.
  Variable history : Z -> Event.

  Abbreviation takes := (takes T N).
  Abbreviation settles := (settles T).
  Abbreviation follows := (follows T N history).

  (** ** What a program does next *)

  Lemma settles_vis X (o : Machine.op code obj X) k q : settles (Vis o k) q -> q = Vis o k.
  Proof. intros H. inversion H. reflexivity. Qed.

  Lemma settles_ret (x : res) q : settles (Ret x) q -> q = Ret x.
  Proof. intros H. inversion H. reflexivity. Qed.

  Lemma settles_call c arg (k : res -> program) q :
    (match c with Init _ => False | _ => True end) -> settles (Call c arg k) q -> q = Call c arg k.
  Proof. intros Hc H. inversion H; subst; [reflexivity | contradiction]. Qed.

  Lemma vis_same X (o o' : Machine.op code obj X) (k k' : X -> program) :
    Vis o k = Vis o' k' -> o = o' /\ k = k'.
  Proof.
    intros H. injection H. intros Hk Ho.
    apply Dependent.EqdepTheory.inj_pair2 in Ho. apply Dependent.EqdepTheory.inj_pair2 in Hk. auto.
  Qed.

  (** ** The event of each operation *)

  Lemma takes_ended a i w e st : takes a i w e Ended st -> False.
  Proof. intros H. inversion H. Qed.

  Lemma takes_waiting a i w e called typed k st :
    takes a i w e (Waiting called typed k) st ->
    exists r spawns x, e = Event_Respond a called r spawns /\ gives N r x /\ typed x /\ st = Running (k x).
  Proof. intros H. inversion H; subst. eauto 8. Qed.

  (** Each way a running call takes an event. *)
  Lemma takes_running a i w e p st :
    takes a i w e (Running p) st ->
    (exists X (o : Machine.op code obj X) k x, settles p (Vis o k) /\ op_event T N a i o x e /\ st = Running (k x)) \/
    (exists m args k ys, settles p (Vis (ExtCall 0 m args) k) /\ Forall2 (names N) ys args /\
       e = Event_Invoke a (Some i) (Invocation_mk m ys) /\ st = Waiting w (returns m) k) \/
    (exists m args k ys r spawns x, settles p (Vis (ExtCall 0 m args) k) /\ Forall2 (names N) ys args /\
       e = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns /\ gives N r x /\ returns m x /\
       st = Running (k x)) \/
    (exists s on args k ys, settles p (Call (Method s) (VList (on :: args)) k) /\
       Forall2 (names N) ys (receiver on ++ args) /\
       e = Event_Invoke a (Some i) (Invocation_mk (label_of s) ys) /\ st = Waiting w (fun _ => True) k) \/
    (exists c arg k m y ys, settles p (Call c arg k) /\
       (match c with Fn _ _ _ | Thunk _ _ => True | _ => False end) /\ called_as c arg m /\
       names N y (VCode c) /\ Forall2 (names N) ys (arguments arg) /\
       e = Event_Invoke a (Some i) (Invocation_mk m (y :: ys)) /\ st = Waiting w (fun _ => True) k) \/
    (exists x r, settles p (Ret x) /\ e = Event_Respond a i r [] /\ gives N r x /\ st = Ended) \/
    (exists X (o : Machine.op code obj X) k, settles p (Vis o k) /\ unsaid o /\ st = Lost).
  Proof.
    intros H. inversion H; subst.
    - left. eauto 10.
    - right; left. eauto 10.
    - right; right; left. eauto 15.
    - right; right; right; left. eauto 10.
    - right; right; right; right; left. eauto 15.
    - right; right; right; right; right; left. eauto 10.
    - right; right; right; right; right; right. eauto 10.
  Qed.

  Lemma takes_ret a i w e (x : res) st :
    takes a i w e (Running (Ret x)) st -> exists r, e = Event_Respond a i r [] /\ gives N r x /\ st = Ended.
  Proof.
    intros H. apply takes_running in H as
      [(X & o & k & x0 & Hs & _) | [(m & args & k & ys & Hs & _) | [(m & args & k & ys & r & sp & x0 & Hs & _) |
      [(s & on & args & k & ys & Hs & _) | [(c & arg & k & m & y & ys & Hs & _) | [(x0 & r & Hs & He & Hg & ->) |
      (X & o & k & Hs & _)]]]]]]; apply settles_ret in Hs; try discriminate Hs.
    injection Hs. intros ->. eauto.
  Qed.

  Lemma takes_outside a i w e m args (k : res -> program) st :
    takes a i w e (Running (Vis (ExtCall 0 m args) k)) st ->
    exists ys, Forall2 (names N) ys args /\
      ((e = Event_Invoke a (Some i) (Invocation_mk m ys) /\ st = Waiting w (returns m) k) \/
       (exists r spawns x, e = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns /\ gives N r x /\
          returns m x /\ st = Running (k x))).
  Proof.
    intros H. apply takes_running in H as
      [(X & o & k0 & x0 & Hs & Hop & _) | [(m0 & args0 & k0 & ys & Hs & Hn & -> & ->) |
      [(m0 & args0 & k0 & ys & r & sp & x0 & Hs & Hn & -> & Hg & Hr & ->) |
      [(s & on & args0 & k0 & ys & Hs & _) | [(c & arg & k0 & m0 & y & ys & Hs & _) | [(x0 & r & Hs & _) |
      (X & o & k0 & Hs & Hu & _)]]]]]]; apply settles_vis in Hs; try discriminate Hs.
    - exfalso. injection Hs. intros _ _ HX. subst X. apply vis_same in Hs as [Ho _]. subst o. exact Hop.
    - apply vis_same in Hs as [Ho ->]. injection Ho. intros -> ->. eauto 8.
    - apply vis_same in Hs as [Ho ->]. injection Ho. intros -> ->. eauto 12.
    - exfalso. injection Hs. intros _ _ HX. subst X. apply vis_same in Hs as [Ho _]. subst o. exact Hu.
  Qed.

  (** An operation on an object of the code: the event it is. *)
  Lemma takes_op_of a i w e X (o : Machine.op code obj X) (k : X -> program) st :
    (forall m args, existT (Machine.op code obj) X o <> existT _ _ (ExtCall 0 m args)) -> ~ unsaid o ->
    takes a i w e (Running (Vis o k)) st -> exists x, op_event T N a i o x e /\ st = Running (k x).
  Proof.
    intros Hext Hsaid H. apply takes_running in H as
      [(X0 & o0 & k0 & x0 & Hs & Hop & ->) | [(m0 & args0 & k0 & ys & Hs & _) |
      [(m0 & args0 & k0 & ys & r & sp & x0 & Hs & _) |
      [(s & on & args0 & k0 & ys & Hs & _) | [(c & arg & k0 & m0 & y & ys & Hs & _) | [(x0 & r & Hs & _) |
      (X0 & o0 & k0 & Hs & Hu & _)]]]]]]; apply settles_vis in Hs; try discriminate Hs.
    - injection Hs. intros _ _ HX. subst X0. apply vis_same in Hs as [Ho Hk]. subst o0 k0. eauto.
    - exfalso. injection Hs. intros _ _ HX. subst X. apply vis_same in Hs as [Ho _]. subst o. eapply Hext. reflexivity.
    - exfalso. injection Hs. intros _ _ HX. subst X. apply vis_same in Hs as [Ho _]. subst o. eapply Hext. reflexivity.
    - exfalso. injection Hs. intros _ _ HX. subst X0. apply vis_same in Hs as [Ho _]. subst o0. exact (Hsaid Hu).
  Qed.

  Lemma takes_read a i w e r f (k : exn + val -> program) st :
    takes a i w e (Running (Vis (ObjGet r f) k)) st ->
    exists v y yo, at_place N yo r /\ names N y v /\ field_typed T (class_at N r) f v /\
      e = Event_Read a (Some i) yo (field_label T (class_at N r) f) y /\ st = Running (k (inr v)).
  Proof.
    intros H. apply takes_op_of in H as (x & (v & y & yo & -> & H) & ->);
      [| intros m args E; apply Dependent.EqdepTheory.inj_pair2 in E; discriminate E | intros []].
    destruct H as (? & ? & ? & ?). eauto 10.
  Qed.

  Lemma takes_method_call a i w e s on args (k : res -> program) st :
    takes a i w e (Running (Call (Method s) (VList (on :: args)) k)) st ->
    exists ys, Forall2 (names N) ys (receiver on ++ args) /\
      e = Event_Invoke a (Some i) (Invocation_mk (label_of s) ys) /\ st = Waiting w (fun _ => True) k.
  Proof.
    intros H. apply takes_running in H as
      [(X0 & o0 & k0 & x0 & Hs & _) | [(m0 & args0 & k0 & ys & Hs & _) |
      [(m0 & args0 & k0 & ys & r & sp & x0 & Hs & _) |
      [(s0 & on0 & args0 & k0 & ys & Hs & Hn & -> & ->) | [(c & arg & k0 & m0 & y & ys & Hs & Hc & _) |
      [(x0 & r & Hs & _) | (X0 & o0 & k0 & Hs & _)]]]]]]; (apply settles_call in Hs; [| exact I]); try discriminate Hs.
    - injection Hs. intros. subst. eauto.
    - exfalso. injection Hs. intros. subst. exact Hc.
  Qed.

  Lemma takes_function_call a i w e c arg (k : res -> program) st :
    (match c with Fn _ _ _ | Thunk _ _ => True | _ => False end) ->
    takes a i w e (Running (Call c arg k)) st ->
    exists m y ys, called_as c arg m /\ names N y (VCode c) /\ Forall2 (names N) ys (arguments arg) /\
      e = Event_Invoke a (Some i) (Invocation_mk m (y :: ys)) /\ st = Waiting w (fun _ => True) k.
  Proof.
    intros Hc H. assert (match c with Init _ => False | _ => True end) as Hi by (destruct c; tauto).
    apply takes_running in H as
      [(X0 & o0 & k0 & x0 & Hs & _) | [(m0 & args0 & k0 & ys & Hs & _) |
      [(m0 & args0 & k0 & ys & r & sp & x0 & Hs & _) |
      [(s0 & on0 & args0 & k0 & ys & Hs & _) | [(c0 & arg0 & k0 & m0 & y & ys & Hs & _ & Ha & Hy & Hys & -> & ->) |
      [(x0 & r & Hs & _) | (X0 & o0 & k0 & Hs & _)]]]]]]; (apply settles_call in Hs; [| exact Hi]); try discriminate Hs.
    - exfalso. injection Hs. intros. subst. exact Hc.
    - injection Hs. intros. subst. eauto 10.
  Qed.

  (** ** A call's own response

      The response of the call made at `i` is the event of a program that has ended, and of no other stage. *)

  Lemma respond_ret a i w r spawns (x : res) st :
    takes a i w (Event_Respond a i r spawns) (Running (Ret x)) st -> gives N r x.
  Proof. intros H. apply takes_ret in H as (r' & He & Hg & _). injection He. intros _ <-. exact Hg. Qed.

  Lemma respond_vis a i w r spawns X (o : Machine.op code obj X) (k : X -> program) st :
    ~ unsaid o -> takes a i w (Event_Respond a i r spawns) (Running (Vis o k)) st -> False.
  Proof.
    intros Hsaid H. apply takes_running in H as
      [(X0 & o0 & k0 & x0 & Hs & Hop & _) | [(m0 & args0 & k0 & ys & _ & _ & He & _) |
      [(m0 & args0 & k0 & ys & r0 & sp & x0 & _ & _ & He & _) |
      [(s & on & args0 & k0 & ys & _ & _ & He & _) | [(c & arg & k0 & m0 & y & ys & _ & _ & _ & _ & _ & He & _) |
      [(x0 & r0 & Hs & _) | (X0 & o0 & k0 & Hs & Hu & _)]]]]]]; try discriminate He.
    - destruct o0; cbn in Hop; try contradiction.
      + destruct Hop as (? & ? & ? & _ & _ & _ & _ & He). discriminate He.
      + destruct Hop as (? & ? & ? & _ & _ & _ & _ & He). discriminate He.
      + destruct Hop as (? & _ & _ & He). discriminate He.
      + destruct Hop as (? & ? & _ & _ & _ & He). discriminate He.
      + destruct Hop as (? & ? & _ & He & _). discriminate He.
    - apply settles_vis in Hs. discriminate Hs.
    - apply settles_vis in Hs. injection Hs. intros _ _ HX. subst X0.
      apply vis_same in Hs as [Ho _]. subst o0. exact (Hsaid Hu).
  Qed.

  Lemma respond_call a i w r spawns c arg (k : res -> program) st :
    (match c with Init _ => False | _ => True end) ->
    takes a i w (Event_Respond a i r spawns) (Running (Call c arg k)) st -> False.
  Proof.
    intros Hc H. apply takes_running in H as
      [(X0 & o0 & k0 & x0 & Hs & _) | [(m0 & args0 & k0 & ys & Hs & _ & He & _) |
      [(m0 & args0 & k0 & ys & r0 & sp & x0 & Hs & _ & He & _) |
      [(s & on & args0 & k0 & ys & Hs & _ & He & _) | [(c0 & arg0 & k0 & m0 & y & ys & Hs & _ & _ & _ & _ & He & _) |
      [(x0 & r0 & Hs & _) | (X0 & o0 & k0 & Hs & _)]]]]]]; try discriminate He;
      apply (settles_call Hc) in Hs; discriminate Hs.
  Qed.

  Lemma respond_waiting a i w r spawns called typed k st :
    takes a i w (Event_Respond a i r spawns) (Waiting called typed k) st -> called = i.
  Proof. intros H. apply takes_waiting in H as (r' & sp & x & He & _). injection He. auto. Qed.

  (** ** A call from one moment to a later one *)

  (** The call made at `i` by `a`, at the stage `st0` before the moment `w0`, is at `st` before `w`. *)
  Inductive steps (a : Value) (i : Z) : Z -> stage -> Z -> stage -> Prop :=
    | steps_here w st : steps a i w st w st
    | steps_other w0 st0 w st :
        ~ its st0 a i (history w0) -> steps a i (w0 + 1) st0 w st -> steps a i w0 st0 w st
    | steps_own w0 st0 st1 w st :
        its st0 a i (history w0) -> takes a i w0 (history w0) st0 st1 -> steps a i (w0 + 1) st1 w st ->
        steps a i w0 st0 w st.

  Lemma steps_later a i w0 st0 w st : steps a i w0 st0 w st -> w0 <= w.
  Proof. induction 1; lia. Qed.

  Lemma steps_more a i w0 st0 w st :
    steps a i w0 st0 w st ->
    (~ its st a i (history w) -> steps a i w0 st0 (w + 1) st) /\
    (forall st', its st a i (history w) -> takes a i w (history w) st st' -> steps a i w0 st0 (w + 1) st').
  Proof.
    induction 1 as [w st | w0 st0 w st Hn _ [IH1 IH2] | w0 st0 st1 w st Hi Ht _ [IH1 IH2]].
    - split; [intros Hn | intros st' Hi Ht].
      + apply steps_other; [exact Hn | apply steps_here].
      + eapply steps_own; [exact Hi | exact Ht | apply steps_here].
    - split; [intros Hn' | intros st' Hi Ht]; apply steps_other; auto.
    - split; [intros Hn' | intros st' Hi' Ht']; eapply steps_own; eauto.
  Qed.

  (** What `follows` gives: the call's stages, each reached from its start, and the step of each event of its
      own. *)
  Lemma follows_steps a i p :
    follows a i p -> exists at_ : Z -> stage,
      (forall w, i < w -> steps a i (i + 1) (Running p) w (at_ w)) /\
      (forall w, i < w -> its (at_ w) a i (history w) -> takes a i w (history w) (at_ w) (at_ (w + 1))).
  Proof.
    intros (at_ & H0 & H). exists at_. split; [| intros w Hw; apply (H w Hw)].
    assert (forall n : nat, steps a i (i + 1) (Running p) (i + 1 + Z.of_nat n) (at_ (i + 1 + Z.of_nat n))) as Hn.
    { induction n as [| n IH].
      - replace (i + 1 + Z.of_nat 0) with (i + 1) by lia. rewrite H0. apply steps_here.
      - replace (i + 1 + Z.of_nat (S n)) with (i + 1 + Z.of_nat n + 1) by lia.
        destruct (H (i + 1 + Z.of_nat n) ltac:(lia)) as [Hown Hother].
        destruct (classic (its (at_ (i + 1 + Z.of_nat n)) a i (history (i + 1 + Z.of_nat n)))) as [Hi | Hi].
        + apply (proj2 (steps_more IH) _ Hi (Hown Hi)).
        + rewrite (Hother Hi). apply (proj1 (steps_more IH) Hi). }
    intros w Hw. specialize (Hn (Z.to_nat (w - (i + 1)))).
    replace (i + 1 + Z.of_nat (Z.to_nat (w - (i + 1)))) with w in Hn by lia. exact Hn.
  Qed.

  (** The call's next event of its own, if it has one before `w`. *)
  Lemma steps_next a i w0 st0 w st :
    steps a i w0 st0 w st ->
    (st = st0 /\ forall v, w0 <= v < w -> ~ its st0 a i (history v)) \/
    exists w1 st1, w0 <= w1 < w /\ (forall v, w0 <= v < w1 -> ~ its st0 a i (history v)) /\
      its st0 a i (history w1) /\ takes a i w1 (history w1) st0 st1 /\ steps a i (w1 + 1) st1 w st.
  Proof.
    induction 1 as [w st | w0 st0 w st Hn Hs IH | w0 st0 st1 w st Hi Ht Hs _].
    - left. split; [reflexivity | intros v Hv; lia].
    - destruct IH as [[-> Hq] | (w1 & st1 & Hw & Hq & Hi & Ht & Hrest)].
      + left. split; [reflexivity |]. intros v Hv. destruct (Z.eq_dec v w0) as [-> | Hne]; [exact Hn | apply Hq; lia].
      + right. exists w1, st1. repeat split; try lia; auto.
        intros v Hv. destruct (Z.eq_dec v w0) as [-> | Hne]; [exact Hn | apply Hq; lia].
    - right. exists w0, st1. pose proof (steps_later Hs). repeat split; try lia; auto.
  Qed.

  (** No event of the call's own from `w0` to `w`. *)
  Definition quiet (a : Value) (i w0 w : Z) : Prop := forall v, w0 <= v < w -> ~ direct a i (history v).

  (** No response to the call made at `called` from `w0` to `w`. *)
  Definition unanswered (a : Value) (called w0 w : Z) : Prop :=
    forall v r spawns, w0 <= v < w -> history v <> Event_Respond a called r spawns.

  Lemma steps_running a i w0 p w st :
    steps a i w0 (Running p) w st ->
    (st = Running p /\ quiet a i w0 w) \/
    exists w1 st1, w0 <= w1 < w /\ quiet a i w0 w1 /\ direct a i (history w1) /\
      takes a i w1 (history w1) (Running p) st1 /\ steps a i (w1 + 1) st1 w st.
  Proof.
    intros H. apply steps_next in H as [[-> Hq] | (w1 & st1 & Hw & Hq & [Hi | []] & Ht & H)].
    - left. split; [reflexivity |]. intros v Hv Hd. apply (Hq v Hv). left. exact Hd.
    - right. exists w1, st1. repeat split; try lia; auto. intros v Hv Hd. apply (Hq v Hv). left. exact Hd.
  Qed.

  Lemma steps_waiting a i w0 called typed k w st :
    steps a i w0 (Waiting called typed k) w st ->
    (st = Waiting called typed k /\ quiet a i w0 w /\ unanswered a called w0 w) \/
    exists w1 r spawns x, w0 <= w1 < w /\ quiet a i w0 w1 /\ unanswered a called w0 w1 /\
      history w1 = Event_Respond a called r spawns /\ gives N r x /\ typed x /\
      steps a i (w1 + 1) (Running (k x)) w st.
  Proof.
    assert (forall w', (forall v, w0 <= v < w' -> ~ its (Waiting called typed k) a i (history v)) ->
      quiet a i w0 w' /\ unanswered a called w0 w') as Hquiet.
    { intros w' Hq. split.
      - intros v Hv Hd. apply (Hq v Hv). left. exact Hd.
      - intros v r sp Hv He. apply (Hq v Hv). right. rewrite He. cbn. auto. }
    intros H. apply steps_next in H as [[-> Hq] | (w1 & st1 & Hw & Hq & _ & Ht & H)].
    - left. destruct (Hquiet w Hq). auto.
    - right. apply takes_waiting in Ht as (r & sp & x & He & Hg & Hty & ->). destruct (Hquiet w1 Hq).
      exists w1, r, sp, x. repeat split; try lia; auto.
  Qed.

  (** A call that has ended makes no event of its own. *)
  Lemma steps_ended a i w0 w st : steps a i w0 Ended w st -> st = Ended /\ quiet a i w0 w.
  Proof.
    intros H. apply steps_next in H as [[-> Hq] | (w1 & st1 & _ & _ & _ & Ht & _)].
    - split; [reflexivity |]. intros v Hv Hd. apply (Hq v Hv). left. exact Hd.
    - exfalso. exact (takes_ended Ht).
  Qed.

  (** ** A call's next step, by what its program does next

      Each says: the call has not taken the step by `w` (and is where it was); or it has, at a moment `w1`, by
      the event the operation is, and goes on from there. *)

  Lemma step_read a i w0 r f (k : exn + val -> program) w st :
    steps a i w0 (Running (Vis (ObjGet r f) k)) w st ->
    (st = Running (Vis (ObjGet r f) k) /\ quiet a i w0 w) \/
    exists w1 v y yo, w0 <= w1 < w /\ quiet a i w0 w1 /\ at_place N yo r /\ names N y v /\
      field_typed T (class_at N r) f v /\
      history w1 = Event_Read a (Some i) yo (field_label T (class_at N r) f) y /\
      steps a i (w1 + 1) (Running (k (inr v))) w st.
  Proof.
    intros H. apply steps_running in H as [H | (w1 & st1 & Hw & Hq & _ & Ht & H)]; [left; exact H | right].
    apply takes_read in Ht as (v & y & yo & Hyo & Hy & Hty & He & ->). exists w1, v, y, yo. auto 10.
  Qed.

  (** A call of what is outside the code: not made yet; made and not responded to; made and responded to; or
      made and responded to at once. *)
  Lemma step_outside a i w0 m args (k : res -> program) w st :
    steps a i w0 (Running (Vis (ExtCall 0 m args) k)) w st ->
    (st = Running (Vis (ExtCall 0 m args) k) /\ quiet a i w0 w) \/
    exists w1 ys, w0 <= w1 < w /\ quiet a i w0 w1 /\ Forall2 (names N) ys args /\
      ((history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) /\
          ((st = Waiting w1 (returns m) k /\ quiet a i (w1 + 1) w /\ unanswered a w1 (w1 + 1) w) \/
           exists w2 r spawns x, w1 < w2 < w /\ quiet a i (w1 + 1) w2 /\ unanswered a w1 (w1 + 1) w2 /\
             history w2 = Event_Respond a w1 r spawns /\ gives N r x /\ returns m x /\
             steps a i (w2 + 1) (Running (k x)) w st)) \/
       (exists r spawns x, history w1 = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns /\ gives N r x /\
          returns m x /\ steps a i (w1 + 1) (Running (k x)) w st)).
  Proof.
    intros H. apply steps_running in H as [H | (w1 & st1 & Hw & Hq & _ & Ht & H)]; [left; exact H | right].
    apply takes_outside in Ht as (ys & Hys & [[He ->] | (r & sp & x & He & Hg & Hr & ->)]);
      exists w1, ys; repeat split; try lia; auto.
    - left. split; [exact He |].
      apply steps_waiting in H as [(-> & Hq2 & Hu) | (w2 & r & sp & x & Hw2 & Hq2 & Hu & He2 & Hg & Hr & H)].
      + left. auto.
      + right. exists w2, r, sp, x. repeat split; try lia; auto.
    - right. exists r, sp, x. auto.
  Qed.

  (** A call inside the call made at `i`, made at `w1` and responded to with `r` before `w2`: by an event made
      and responded to at once, or by a response to it. *)
  Definition done_inside (a : Value) (i : Z) (m : string) (ys : list Value) (w1 : Z) (r : Response) (w2 : Z) : Prop :=
    (exists spawns, history w1 = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns /\ w2 = w1 + 1) \/
    (history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) /\ w1 < w2 - 1 /\
       exists spawns, history (w2 - 1) = Event_Respond a w1 r spawns).

  (** The same as `step_outside`, the two ways a call is responded to as one. *)
  Lemma step_called a i w0 m args (k : res -> program) w st :
    steps a i w0 (Running (Vis (ExtCall 0 m args) k)) w st ->
    (st = Running (Vis (ExtCall 0 m args) k) /\ quiet a i w0 w) \/
    exists w1 ys, w0 <= w1 < w /\ quiet a i w0 w1 /\ Forall2 (names N) ys args /\
      ((history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) /\ st = Waiting w1 (returns m) k /\
          quiet a i (w1 + 1) w /\ unanswered a w1 (w1 + 1) w) \/
       exists w2 r x, w1 < w2 <= w /\ quiet a i (w1 + 1) (w2 - 1) /\ done_inside a i m ys w1 r w2 /\ gives N r x /\
         returns m x /\ steps a i w2 (Running (k x)) w st).
  Proof.
    intros H. apply step_outside in H as [H | (w1 & ys & Hw & Hq & Hys & H)]; [left; exact H | right].
    exists w1, ys. repeat split; try lia; auto.
    destruct H as [[He [(-> & Hq2 & Hu) | (w2 & r & sp & x & Hw2 & Hq2 & Hu & He2 & Hg & Hr & H)]] |
      (r & sp & x & He & Hg & Hr & H)].
    - left. auto.
    - right. exists (w2 + 1), r, x. replace (w2 + 1 - 1) with w2 by lia. pose proof (steps_later H).
      repeat split; try lia; auto. right. replace (w2 + 1 - 1) with w2 by lia. repeat split; try lia; eauto.
    - right. exists (w1 + 1), r, x. pose proof (steps_later H). repeat split; try lia; auto.
      + intros v Hv. lia.
      + left. eauto.
  Qed.

  (** A call of a method of the code: made, and then responded to with what the method gave. *)
  Lemma step_method a i w0 s on args (k : res -> program) w st :
    steps a i w0 (Running (Call (Method s) (VList (on :: args)) k)) w st ->
    (st = Running (Call (Method s) (VList (on :: args)) k) /\ quiet a i w0 w) \/
    exists w1 ys, w0 <= w1 < w /\ quiet a i w0 w1 /\ Forall2 (names N) ys (receiver on ++ args) /\
      history w1 = Event_Invoke a (Some i) (Invocation_mk (label_of s) ys) /\
      ((st = Waiting w1 (fun _ => True) k /\ quiet a i (w1 + 1) w /\ unanswered a w1 (w1 + 1) w) \/
       exists w2 r spawns x, w1 < w2 < w /\ quiet a i (w1 + 1) w2 /\ unanswered a w1 (w1 + 1) w2 /\
         history w2 = Event_Respond a w1 r spawns /\ gives N r x /\ steps a i (w2 + 1) (Running (k x)) w st).
  Proof.
    intros H. apply steps_running in H as [H | (w1 & st1 & Hw & Hq & _ & Ht & H)]; [left; exact H | right].
    apply takes_method_call in Ht as (ys & Hys & He & ->). exists w1, ys. repeat split; try lia; auto.
    apply steps_waiting in H as [(-> & Hq2 & Hu) | (w2 & r & sp & x & Hw2 & Hq2 & Hu & He2 & Hg & _ & H)].
    - left. auto.
    - right. exists w2, r, sp, x. repeat split; try lia; auto.
  Qed.

  (** A call of a function. *)
  Lemma step_function a i w0 c arg (k : res -> program) w st :
    (match c with Fn _ _ _ | Thunk _ _ => True | _ => False end) ->
    steps a i w0 (Running (Call c arg k)) w st ->
    (st = Running (Call c arg k) /\ quiet a i w0 w) \/
    exists w1 m y ys, w0 <= w1 < w /\ quiet a i w0 w1 /\ called_as c arg m /\ names N y (VCode c) /\
      Forall2 (names N) ys (arguments arg) /\
      history w1 = Event_Invoke a (Some i) (Invocation_mk m (y :: ys)) /\
      ((st = Waiting w1 (fun _ => True) k /\ quiet a i (w1 + 1) w /\ unanswered a w1 (w1 + 1) w) \/
       exists w2 r spawns x, w1 < w2 < w /\ quiet a i (w1 + 1) w2 /\ unanswered a w1 (w1 + 1) w2 /\
         history w2 = Event_Respond a w1 r spawns /\ gives N r x /\ steps a i (w2 + 1) (Running (k x)) w st).
  Proof.
    intros Hc H. apply steps_running in H as [H | (w1 & st1 & Hw & Hq & _ & Ht & H)]; [left; exact H | right].
    apply (takes_function_call Hc) in Ht as (m & y & ys & Hm & Hy & Hys & He & ->).
    exists w1, m, y, ys. repeat split; try lia; auto.
    apply steps_waiting in H as [(-> & Hq2 & Hu) | (w2 & r & sp & x & Hw2 & Hq2 & Hu & He2 & Hg & _ & H)].
    - left. auto.
    - right. exists w2, r, sp, x. repeat split; try lia; auto.
  Qed.

  (** The call's end: its response is what its program gave, and it makes no event after. *)
  Lemma step_ret a i w0 (x : res) w st :
    steps a i w0 (Running (Ret x)) w st ->
    (st = Running (Ret x) /\ quiet a i w0 w) \/
    exists w1 r, w0 <= w1 < w /\ quiet a i w0 w1 /\ history w1 = Event_Respond a i r [] /\ gives N r x /\
      st = Ended /\ quiet a i (w1 + 1) w.
  Proof.
    intros H. apply steps_running in H as [H | (w1 & st1 & Hw & Hq & _ & Ht & H)]; [left; exact H | right].
    apply takes_ret in Ht as (r & He & Hg & ->). apply steps_ended in H as [-> Hq2]. exists w1, r. auto 10.
  Qed.

  (** A call that has only its result left: its response is that result. *)
  Lemma ends_with a i w0 (x : res) w st r spawns st' :
    steps a i w0 (Running (Ret x)) w st -> takes a i w (Event_Respond a i r spawns) st st' -> gives N r x.
  Proof.
    intros H Hgo. apply step_ret in H as [[-> _] | (w1 & r' & _ & _ & _ & _ & -> & _)].
    - exact (respond_ret Hgo).
    - exfalso. exact (takes_ended Hgo).
  Qed.

  (** ** Values of the execution that are data *)

  Lemma named_bool y (b : bool) : names N y (VBool b) -> y = Value_Bool_ (if b then True else False).
  Proof.
    intros H. rewrite (one_name N y _ _ H (of_bool N b)). f_equal. apply propositional_extensionality.
    destruct b; split; intros; [exact I | reflexivity | discriminate | contradiction].
  Qed.

  Lemma named_unit y : names N y VUnit -> y = Value_Unit_.
  Proof. intros H. exact (one_name N y _ _ H (of_unit N)). Qed.

  Lemma unit_named y v : names N y v -> y = Value_Unit_ -> v = VUnit.
  Proof. intros H ->. exact (names_one N _ _ _ H (of_unit N)). Qed.

  (** The object a value of the execution names is at one place, of one class. *)
  Lemma named_ref y c r c' r' : names N y (vref c r) -> names N y (vref c' r') -> c = c' /\ r = r'.
  Proof. intros H1 H2. pose proof (names_one N _ _ _ H1 H2) as E. injection E. auto. Qed.

  Lemma at_place_of y c r : names N y (vref c r) -> class_at N r = c /\ at_place N y r.
  Proof. intros H. pose proof (ref_class N _ _ _ H) as E. split; [exact E |]. unfold at_place. rewrite E. exact H. Qed.

  (** ** The calls of the code in an execution of it *)

  Hypothesis conformed : conforms files T N history.

  (** A call of a method on an object of the code: its stages, each reached from its start. *)
  Lemma method_steps a inside s cls r d y ys args from :
    history from = Event_Invoke a inside (Invocation_mk (label_of s) (y :: ys)) ->
    names N y (vref cls r) -> impl T cls s = Some d -> Forall2 (names N) ys args -> passed d args ->
    exists at_ : Z -> stage,
      (forall w, from < w ->
        steps a from (from + 1) (Running (run T (Method s) (VList (vref cls r :: args)))) w (at_ w)) /\
      (forall w, from < w -> its (at_ w) a from (history w) -> takes a from w (history w) (at_ w) (at_ (w + 1))).
  Proof.
    intros He Hy Hd Hys Hp. apply follows_steps. eapply (proj1 conformed); [exact He |].
    left. exists s, cls, r, d, y, ys, args. auto 10.
  Qed.

  (** A call of a method of the code is no event made and responded to at once. *)
  Lemma method_not_atomic w a inside s cls r d y ys args resp spawns :
    history w = Event_Atomic a inside (Invocation_mk (label_of s) (y :: ys)) resp spawns ->
    names N y (vref cls r) -> impl T cls s = Some d -> Forall2 (names N) ys args -> passed d args -> False.
  Proof.
    intros He Hy Hd Hys Hp. eapply (proj1 (proj2 conformed)); [exact He |].
    left. exists s, cls, r, d, y, ys, args. repeat split; auto.
  Qed.

  (** A field read of the object a value names is a read of that value's object, of its class. *)
  Lemma read_place y c r yo : names N y (vref c r) -> at_place N yo r -> yo = y /\ class_at N r = c.
  Proof.
    intros Hy Hyo. destruct (at_place_of Hy) as [Hc Hp]. split; [| exact Hc]. exact (one_name N _ _ _ Hyo Hp).
  Qed.

  (** An object the execution says is made is an object of the code, of its class. *)
  Lemma made_named w b inside y cls hs :
    history w = Event_Make b inside y cls hs -> exists r, names N y (vref cls r).
  Proof. intros H. exact (proj1 (proj2 (proj2 conformed)) _ _ _ _ _ _ H). Qed.

End Walk.

(** ** Walking *)

(** What follows a step, set aside under a name: dropped once no hypothesis speaks of it. *)
Ltac walk_clear := repeat match goal with K := _ : _ -> prog _ _ _ _ _ |- _ => clear K end.

(** The stage of a hypothesis that says where a call is, with its program's next step computed: its first
    operation, call or result, with what it is of computed (but what a call is made on, `receiver`: of a value
    not known it is the proof's to say) and what follows it set aside under a name. *)
Ltac walk H :=
  lazymatch type of H with
  | steps ?T ?N ?h ?a ?i ?w0 (Running ?p) ?w ?st =>
      let p' := eval lazy head beta iota zeta delta -[implemented] in p in
      lazymatch p' with
      | Vis ?o ?k =>
          let o' := eval lazy beta iota zeta delta -[receiver] in o in
          let K := fresh "K" in
          pose (K := k); change (steps T N h a i w0 (Running (Vis o' K)) w st) in H; walk_clear;
          (* what the call is made on, where the proof has said it *)
          repeat match goal with E : receiver ?v = _ |- _ => rewrite E in H end; cbn [app] in H
      | Call ?c ?arg ?k =>
          let c' := eval lazy in c in
          let arg' := eval lazy in arg in
          let K := fresh "K" in
          pose (K := k); change (steps T N h a i w0 (Running (Call c' arg' K)) w st) in H; walk_clear
      | Ret ?x =>
          let x' := eval lazy in x in change (steps T N h a i w0 (Running (Ret x')) w st) in H; walk_clear
      | context [implemented ?T' ?v ?s] =>
          (* a call on a value: which method of the code it runs is computed where the value is known; of a
             value not known, none where no class of the code has one *)
          let d := eval lazy in (implemented T' v s) in
          change (steps T N h a i w0 (Running p') w st) in H; walk_clear;
          lazymatch d with
          | Some _ => change (implemented T' v s) with d in H; walk H
          | None => change (implemented T' v s) with d in H; walk H
          | _ =>
              let E := fresh in
              assert (E : unimplemented T' s = true) by (vm_compute; reflexivity);
              rewrite (implemented_none T' s v E) in H; clear E; walk H
          end
      | _ => change (steps T N h a i w0 (Running p') w st) in H; walk_clear
      end
  end.
