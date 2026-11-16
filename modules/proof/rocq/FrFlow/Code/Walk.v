(** A call of the code from one moment to a later one.

    `conforms` gives, for a call of the code, the stage it is at before each moment (`follows`). Here that is
    said as a relation between moments (`steps`): the call goes from a stage to a later one by its own events,
    each the event of what its program does next (`takes_read`, `takes_outside`, `takes_method_call`, …), other
    events leaving it where it is. `method_steps` and `function_steps` say it of a call in an execution of the
    code. The rules a proof of a claim uses are built on these (`FrFlow.Code.Logic`). *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Ascii Lia Classical_Prop ProofIrrelevanceFacts.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Equal FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Code.Outside FrFlow.Code.Conforms.
Require Export FrFlow.Code.Classes.
Require FrFlow.Scala.Jdk.
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
  | Value_Thrown cls => Some (VExn (made_exn cls))
  | Value_Null => Some vnull
  end.

Lemma truths_differ : (false = true) <> (true = true).
Proof. intros H. assert (false = true) as F by (rewrite H; reflexivity). discriminate F. Qed.

(** Two classes of what the JDK throws give two exceptions. *)
Lemma made_exn_one (a b : string) : made_exn a = made_exn b -> a = b.
Proof.
  unfold made_exn.
  repeat match goal with |- context [String.eqb ?x ?y] => destruct (String.eqb_spec x y) end;
    intros H; subst; try discriminate H; try reflexivity; injection H; auto.
Qed.

Lemma plain_one (x y : Value) (v : val) : plain_val x = Some v -> plain_val y = Some v -> x = y.
Proof.
  destruct x as [| P | z | s | r | c |], y as [| Q | z' | s' | r' | c' |]; cbn; try congruence;
    repeat match goal with |- context [excluded_middle_informative ?A] => destruct (excluded_middle_informative A) end;
    try congruence; intros H1 H2; rewrite <- H2 in H1; try discriminate H1; injection H1; intros;
    first [congruence | f_equal; apply made_exn_one; congruence].
Qed.

Definition plain_naming : naming.
Proof.
  refine (Naming plain_val (fun _ => "") eq_refl _ (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)
    eq_refl plain_one _).
  - intros [|]; cbn.
    + destruct (excluded_middle_informative _) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
    + destruct (excluded_middle_informative _) as [e | _]; [exfalso; exact (truths_differ e) |].
      destruct (excluded_middle_informative _) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
  - intros [| P | z | s | r | cls |] c r'; cbn; try discriminate;
      repeat destruct (excluded_middle_informative _); discriminate.
Defined.

Lemma nothing_runs (files : list tree) (T : table) (known : classes) : runs files T known (fun _ => Event_Stutter).
Proof.
  exists plain_naming. repeat split.
  - intros i a inside s cls r d y ys H. discriminate H.
  - intros i a inside owner name signature c d ys H. discriminate H.
  - intros i a inside m c y ys H. discriminate H.
  - intros s cls r d y ys' _ _ _ _. discriminate H.
  - intros owner name signature c d _ _ _ _. discriminate H.
  - intros c y ys' _ _ _ _. discriminate H.
  - intros w b inside y cls hs H. discriminate H.
  - intros w w' b inside y cls hs b' inside' cls' hs' H. discriminate H.
  - intros k k' a called r r' spawns spawns' H. discriminate H.
  - intros k a called r spawns H. discriminate H.
Qed.

Set Implicit Arguments.

(** ** Two references compared

    Whether two references are the same is decided where no class of the code says what `equals` is: they are
    the same value or they are not. *)
Lemma equal_identity (T : table) (a b : val) :
  identity a -> identity b -> unnamed T "equals" = true -> equal T a b = oret (val_eqb a b).
Proof.
  intros Ha Hb HT.
  assert (forall x y : val, x <> y -> val_eqb x y = false) as Hne.
  { intros x y H. unfold val_eqb. destruct (val_eq_dec x y); [contradiction | reflexivity]. }
  destruct a as [| | ta | | oa | |]; try contradiction; destruct b as [| | tb | | ob | |]; try contradiction;
    try (destruct oa; try contradiction); try (destruct ob; try contradiction); unfold equal; cbn;
    try rewrite (named_none T "equals" _ HT); cbn;
    try (rewrite Hne by discriminate; reflexivity).
  all: unfold same_place;
    repeat match goal with |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y) as [-> | ?]; cbn end;
    repeat match goal with |- context [String.eqb ?x ?y] => destruct (String.eqb_spec x y) as [-> | ?]; cbn end;
    first [reflexivity | rewrite val_eqb_refl; reflexivity | rewrite Hne by congruence; reflexivity].
Qed.

(** Any value compared with a reference known by its identity, where no class of the code says what `equals`
    is: it is that reference or it is not. *)
Lemma equal_to_identity (T : table) (a b : val) :
  identity b -> unnamed T "equals" = true -> equal T a b = oret (val_eqb a b).
Proof.
  intros Hb HT.
  assert (forall x y : val, x <> y -> val_eqb x y = false) as Hne.
  { intros x y H. unfold val_eqb. destruct (val_eq_dec x y); [contradiction | reflexivity]. }
  destruct b as [| | tb | | ob | |]; try contradiction; try (destruct ob; try contradiction);
    destruct a as [| | ta | | oa | |]; try destruct oa; unfold equal; cbn;
    try rewrite (named_none T "equals" _ HT); cbn; try (rewrite Hne by discriminate; reflexivity).
  all: unfold same_place;
    repeat match goal with |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y) as [-> | ?]; cbn end;
    repeat match goal with |- context [String.eqb ?x ?y] => destruct (String.eqb_spec x y) as [-> | ?]; cbn end;
    first [reflexivity | rewrite val_eqb_refl; reflexivity | rewrite Hne by congruence; reflexivity].
Qed.

(** Whether one of some values meets a test that is decided: decided (`some_of`, kept as it is where a program
    is computed). So is a value among those of a set that does not change, where the value is a reference known
    by its identity. *)
Definition some_of (f : val -> bool) (xs : list val) : bool := existsb f xs.

Lemma any_decided (p : val -> X bool) (f : val -> bool) (xs : list val) :
  (forall y, p y = oret (f y)) -> any p xs = oret (some_of f xs).
Proof.
  intros H. unfold some_of. induction xs as [| x rest IH]; [reflexivity |]. cbn. rewrite H. cbn.
  destruct (f x); [reflexivity | exact IH].
Qed.

(** A value compared with `null`: it is `null` or it is not, whatever it is. *)
Lemma equal_null (T : table) (v : val) : equal T v vnull = oret (val_eqb v vnull).
Proof.
  assert (forall w, w <> vnull -> val_eqb w vnull = false) as Hne.
  { intros w Hw. unfold val_eqb. destruct (val_eq_dec w vnull) as [E | _]; [destruct (Hw E) | reflexivity]. }
  destruct v as [| | | | o | |]; try (rewrite Hne by discriminate; reflexivity).
  destruct o; try (rewrite Hne by discriminate; reflexivity). rewrite val_eqb_refl. reflexivity.
Qed.

(** ** A function the code wrote, decided by looking for its tree among the code's *)
Definition among (files : list tree) (t : tree) : bool :=
  if in_dec tree_eq_dec t (over_list nodes files) then true else false.

Lemma written_function (files : list tree) (d : tree) (sc : scope) (group : list tree) :
  among files d = true -> written files (Fn d sc group).
Proof. unfold among. destruct (in_dec tree_eq_dec d (over_list nodes files)); [auto | discriminate]. Qed.

(** A call of what is outside the code. *)
Definition outside_call {X : Type} (o : Machine.op code obj X) : Prop :=
  match o with ExtCall 0 _ _ => True | _ => False end.

Section Walk.

  Variable files : list tree.
  Variable T : table.
  Variable known : classes.
  Variable N : naming.
  Variable history : Z -> Event.

  Abbreviation takes := (takes T known N).
  Abbreviation settles := (settles T).
  Abbreviation follows := (follows T known N history).

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
    (exists X (o : Machine.op code obj X) k x,
       settles p (Vis o k) /\ op_event T known N a i o x e /\ st = Running (k x)) \/
    (exists m args k ys, settles p (Vis (ExtCall 0 m args) k) /\ Forall2 (names N) ys args /\
       e = Event_Invoke a (Some i) (Invocation_mk m ys) /\ st = Waiting w (returns known m) k) \/
    (exists m args k ys r spawns x, settles p (Vis (ExtCall 0 m args) k) /\ Forall2 (names N) ys args /\
       e = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns /\ gives N r x /\ returns known m x /\
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
      ((e = Event_Invoke a (Some i) (Invocation_mk m ys) /\ st = Waiting w (returns known m) k) \/
       (exists r spawns x, e = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns /\ gives N r x /\
          returns known m x /\ st = Running (k x))).
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
    ~ outside_call o -> ~ unsaid o ->
    takes a i w e (Running (Vis o k)) st -> exists x, op_event T known N a i o x e /\ st = Running (k x).
  Proof.
    intros Hext Hsaid H. apply takes_running in H as
      [(X0 & o0 & k0 & x0 & Hs & Hop & ->) | [(m0 & args0 & k0 & ys & Hs & _) |
      [(m0 & args0 & k0 & ys & r & sp & x0 & Hs & _) |
      [(s & on & args0 & k0 & ys & Hs & _) | [(c & arg & k0 & m0 & y & ys & Hs & _) | [(x0 & r & Hs & _) |
      (X0 & o0 & k0 & Hs & Hu & _)]]]]]]; apply settles_vis in Hs; try discriminate Hs.
    - injection Hs. intros _ _ HX. subst X0. apply vis_same in Hs as [Ho Hk]. subst o0 k0. eauto.
    - exfalso. injection Hs. intros _ _ HX. subst X. apply vis_same in Hs as [Ho _]. subst o. exact (Hext I).
    - exfalso. injection Hs. intros _ _ HX. subst X. apply vis_same in Hs as [Ho _]. subst o. exact (Hext I).
    - exfalso. injection Hs. intros _ _ HX. subst X0. apply vis_same in Hs as [Ho _]. subst o0. exact (Hsaid Hu).
  Qed.

  Lemma takes_read a i w e r f (k : exn + val -> program) st :
    takes a i w e (Running (Vis (ObjGet r f) k)) st ->
    exists v y yo, at_place N yo r /\ names N y v /\ field_typed T known (class_at N r) f v /\
      e = Event_Read a (Some i) yo (field_label T (class_at N r) f) y /\ st = Running (k (inr v)).
  Proof.
    intros H. apply takes_op_of in H as (x & (v & y & yo & -> & H) & ->);
      [| intros [] | intros []].
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
  Proof using T N.
    intros Hc H. assert (match c with Init _ => False | _ => True end) as Hi by (destruct c; try exact I; exact Hc).
    apply takes_running in H as
      [(X0 & o0 & k0 & x0 & Hs & _) | [(m0 & args0 & k0 & ys & Hs & _) |
      [(m0 & args0 & k0 & ys & r & sp & x0 & Hs & _) |
      [(s0 & on0 & args0 & k0 & ys & Hs & _) | [(c0 & arg0 & k0 & m0 & y & ys & Hs & _ & Ha & Hy & Hys & -> & ->) |
      [(x0 & r & Hs & _) | (X0 & o0 & k0 & Hs & _)]]]]]]; (apply settles_call in Hs; [| exact Hi]); try discriminate Hs.
    - exfalso. injection Hs. intros. subst. exact Hc.
    - injection Hs. intros. subst. eauto 10.
  Qed.

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
      (forall w, direct a i (history w) -> i < w) /\
      (forall w, i < w -> steps a i (i + 1) (Running p) w (at_ w)) /\
      (forall w, i < w -> its (at_ w) a i (history w) -> takes a i w (history w) (at_ w) (at_ (w + 1))).
  Proof.
    intros (Hbefore & _ & at_ & H0 & H). exists at_. split; [| split; [| intros w Hw; apply (H w Hw)]].
    { intros w Hd. destruct (Z_lt_le_dec i w) as [Hlt | Hle]; [exact Hlt | destruct (Hbefore w Hle Hd)]. }
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

  (** ** A call made inside the call, and the call's end *)

  (** A call inside the call made at `i`, made at `w1` and responded to with `r` before `w2`: by an event made
      and responded to at once, or by a response to it. *)
  Definition done_inside (a : Value) (i : Z) (m : string) (ys : list Value) (w1 : Z) (r : Response) (w2 : Z) : Prop :=
    (exists spawns, history w1 = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns /\ w2 = w1 + 1) \/
    (history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) /\ w1 < w2 - 1 /\
       exists spawns, history (w2 - 1) = Event_Respond a w1 r spawns).

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

  (** ** Values of the execution that are data *)

  (** A truth value of the execution is the code's: true where it holds. *)
  Lemma bool_named (P : Prop) (b : bool) : names N (Value_Bool_ P) (VBool b) -> (P <-> b = true).
  Proof. intros H. pose proof (one_name N _ _ _ H (of_bool N b)) as E. injection E as ->. tauto. Qed.

  Lemma named_bool y (b : bool) : names N y (VBool b) -> y = Value_Bool_ (if b then True else False).
  Proof.
    intros H. rewrite (one_name N y _ _ H (of_bool N b)). f_equal. apply propositional_extensionality.
    destruct b; split; intros; [exact I | reflexivity | discriminate | contradiction].
  Qed.

  Lemma at_place_of y c r : names N y (vref c r) -> class_at N r = c /\ at_place N y r.
  Proof. intros H. pose proof (ref_class N _ _ _ H) as E. split; [exact E |]. unfold at_place. rewrite E. exact H. Qed.

  (** ** The calls of the code in an execution of it *)

  Hypothesis conformed : conforms files T known N history.

  (** A call of a method on an object of the code: its arguments; that its own events come after it; its
      stages, each reached from its start; and the step of each event of its own. *)
  Lemma method_steps a inside s cls r d y ys from :
    history from = Event_Invoke a inside (Invocation_mk (label_of s) (y :: ys)) ->
    names N y (vref cls r) -> impl T cls s = Some d ->
    exists args (at_ : Z -> stage), Forall2 (names N) ys args /\ passed known d args /\
      (forall w, direct a from (history w) -> from < w) /\
      (forall w, from < w ->
        steps a from (from + 1) (Running (run T (Method s) (VList (vref cls r :: args)))) w (at_ w)) /\
      (forall w, from < w -> its (at_ w) a from (history w) -> takes a from w (history w) (at_ w) (at_ (w + 1))).
  Proof.
    intros He Hy Hd. destruct (proj1 conformed _ _ _ _ _ _ _ _ _ He Hy Hd) as (args & Hys & Hp & Hf).
    apply follows_steps in Hf as (at_ & H0 & H1 & H2). exists args, at_. auto.
  Qed.

  (** A call of a method of the code makes no event of its own once it has responded. *)
  Lemma method_over a inside s cls r d y ys from k w resp spawns :
    history from = Event_Invoke a inside (Invocation_mk (label_of s) (y :: ys)) ->
    names N y (vref cls r) -> impl T cls s = Some d ->
    history k = Event_Respond a from resp spawns -> k < w -> ~ direct a from (history w).
  Proof.
    intros He Hy Hd Hk Hlt. destruct (proj1 conformed _ _ _ _ _ _ _ _ _ He Hy Hd) as (args & _ & _ & Hf).
    exact (proj1 (proj2 Hf) _ _ _ _ Hk Hlt).
  Qed.

  (** A call of a function the code wrote. *)
  Lemma function_steps a inside m c y ys from :
    history from = Event_Invoke a inside (Invocation_mk m (y :: ys)) ->
    applies known m = true -> names N y (VCode c) -> written files c ->
    exists args (at_ : Z -> stage), Forall2 (names N) ys args /\ given known c args /\
      (forall w, direct a from (history w) -> from < w) /\
      (forall w, from < w -> steps a from (from + 1) (Running (run T c (VList args))) w (at_ w)) /\
      (forall w, from < w -> its (at_ w) a from (history w) -> takes a from w (history w) (at_ w) (at_ (w + 1))).
  Proof.
    intros He Hm Hy Hw.
    destruct (proj1 (proj2 (proj2 conformed)) _ _ _ _ _ _ _ He Hm Hy Hw) as (args & Hys & Hg & Hf).
    apply follows_steps in Hf as (at_ & H0 & H1 & H2). exists args, at_. auto.
  Qed.

  (** A call of a method of the code is no event made and responded to at once. *)
  Lemma method_not_atomic w a inside s cls r d y ys resp spawns :
    history w = Event_Atomic a inside (Invocation_mk (label_of s) (y :: ys)) resp spawns ->
    names N y (vref cls r) -> impl T cls s = Some d -> False.
  Proof.
    intros He Hy Hd.
    exact (proj1 (proj1 (proj2 (proj2 (proj2 conformed))) _ _ _ _ _ _ _ He) s cls r d y ys eq_refl eq_refl Hy Hd).
  Qed.

  (** A call of a function the code wrote is no event made and responded to at once. *)
  Lemma function_not_atomic w a inside m c y ys resp spawns :
    history w = Event_Atomic a inside (Invocation_mk m (y :: ys)) resp spawns ->
    applies known m = true -> names N y (VCode c) -> written files c -> False.
  Proof.
    intros He Hm Hy Hw.
    exact (proj2 (proj2 (proj1 (proj2 (proj2 (proj2 conformed))) _ _ _ _ _ _ _ He)) c y ys Hm eq_refl Hy Hw).
  Qed.

  (** A field read of the object a value names is a read of that value's object, of its class. *)
  Lemma read_place y c r yo : names N y (vref c r) -> at_place N yo r -> yo = y /\ class_at N r = c.
  Proof.
    intros Hy Hyo. destruct (at_place_of Hy) as [Hc Hp]. split; [| exact Hc]. exact (one_name N _ _ _ Hyo Hp).
  Qed.

  (** An object the execution says is made is an object of the code, of its class. *)
  Lemma made_named w b inside y cls hs :
    history w = Event_Make b inside y cls hs -> exists r, names N y (vref cls r).
  Proof. intros H. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 conformed))))) _ _ _ _ _ _ H). Qed.

  (** A call is responded to at one moment. *)
  Lemma responded_once k k' a called r r' spawns spawns' :
    history k = Event_Respond a called r spawns -> history k' = Event_Respond a called r' spawns' -> k = k'.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 conformed))))) k k' a called r r' spawns spawns'). Qed.

  (** A call is responded to after it is made. *)
  Lemma responded_after k a called r spawns : history k = Event_Respond a called r spawns -> called < k.
  Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 conformed))))) k a called r spawns). Qed.

End Walk.

Arguments method_steps {files T known N history} conformed {a inside} s {cls r d y ys from} _ _ _.
Arguments method_not_atomic {files T known N history} conformed {w a inside} s {cls r d y ys resp spawns} _ _ _.
Arguments function_steps {files T known N history} conformed {a inside m c y ys from} _ _ _ _.
Arguments made_named {files T known N history} conformed {w b inside y cls hs} _.
Arguments responded_once {files T known N history} conformed {k k' a called r r' spawns spawns'} _ _.
Arguments responded_after {files T known N history} conformed {k a called r spawns} _.
Arguments method_over {files T known N history} conformed {a inside} s {cls r d y ys from k w resp spawns} _ _ _ _ _.
Arguments function_not_atomic {files T known N history} conformed {w a inside m c y ys resp spawns} _ _ _ _.
