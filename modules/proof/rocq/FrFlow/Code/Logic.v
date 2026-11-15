(** What holds at every event of a call's own, one rule for each thing its program does next.

    A claim of code is of the events a call makes itself: "the call that adds a thread has asked the factory
    for it". It is proven of the method's program, read from its tree, by going through the program once:
    at each operation, the rule of that operation asks that the claim hold at the operation's event, and gives
    what the execution says of that event to the rest of the program.

    `meets claim tr w0 st w`: the call, at the stage `st` before the moment `w0`, having made events of its own
    at the moments `tr` and no others, meets the claim at `w` if `w` is an event of its own. Rules:

    - `meets_from`: the claim holds at every moment from here on, whatever the program does;
    - `meets_ret`: the program has its result, and its event is the call's response;
    - `meets_read`, `meets_op`: a field read, an object made, a field written;
    - `meets_called`: a call of what is outside the code, and its response;
    - `meets_method`, `meets_function`: a call of a method of the code, of a function, and its response;
    - `meets_iter`: a loop, by what holds at each turn.

    `method_meets` and `function_meets` say it of a call in an execution of the code: the claim holds at every
    event the call makes itself. The tactics `step` and `pass` apply the rule of what the program does next. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia Classical.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Code.Walk.
Require FrFlow.Scala.Jdk.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Set Implicit Arguments.

Section Logic.

  Variable files : list tree.
  Variable T : table.
  Variable known : classes.
  Variable N : naming.
  Variable history : Z -> Event.

  (** The call: made at `i` by `a`. And what is claimed of each moment at which it makes an event itself. *)
  Variable a : Value.
  Variable i : Z.
  Variable claim : Z -> Prop.

  Abbreviation steps := (steps T known N history a i).
  Abbreviation takes := (takes T known N a i).
  Abbreviation quiet := (quiet history a i).

  (** The event makes the call `inv` inside the call: made, or made and responded to at once. *)
  Definition makes (e : Event) (inv : Invocation) : Prop :=
    e = Event_Invoke a (Some i) inv \/ exists r spawns, e = Event_Atomic a (Some i) inv r spawns.

  Lemma makes_direct e inv : makes e inv -> direct a i e.
  Proof. intros [-> | (r & sp & ->)]; cbn; auto. Qed.

  Lemma makes_one e inv inv' : makes e inv -> makes e inv' -> inv = inv'.
  Proof. intros [-> | (r & sp & ->)] [E | (r' & sp' & E)]; congruence. Qed.

  (** The call's own events before `w0` are at the moments `tr`. *)
  Definition past (w0 : Z) (tr : list Z) : Prop := forall m, m < w0 -> direct a i (history m) -> In m tr.

  Lemma past_quiet w0 w1 tr : past w0 tr -> quiet w0 w1 -> past w1 tr.
  Proof.
    intros Hp Hq m Hm Hd. destruct (Z_lt_le_dec m w0) as [Hlt | Hle]; [exact (Hp m Hlt Hd) |].
    destruct (Hq m ltac:(lia) Hd).
  Qed.

  Lemma past_step w1 tr : past w1 tr -> past (w1 + 1) (w1 :: tr).
  Proof.
    intros Hp m Hm Hd. destruct (Z.eq_dec m w1) as [-> | Hne]; [left; reflexivity | right].
    apply Hp; [lia | exact Hd].
  Qed.

  Definition meets (tr : list Z) (w0 : Z) (st : stage) (w : Z) : Prop :=
    i < w0 -> past w0 tr -> forall stw st',
      steps w0 st w stw -> direct a i (history w) -> takes w (history w) stw st' -> claim w.

  (** ** The next event of a running call, whatever it is *)

  Lemma meets_running tr w0 p w :
    (forall w1 st1, i < w1 -> w0 <= w1 -> past w1 tr -> direct a i (history w1) ->
       takes w1 (history w1) (Running p) st1 -> claim w1 /\ meets (w1 :: tr) (w1 + 1) st1 w) ->
    meets tr w0 (Running p) w.
  Proof.
    intros H Hi Hp stw st' Hs Hd Ht. pose proof (steps_later Hs) as Hle.
    apply steps_running in Hs as [[-> Hq] | (w1 & st1 & Hw & Hq & Hd1 & Ht1 & Hs)].
    - exact (proj1 (H w st' ltac:(lia) Hle (past_quiet Hp Hq) Hd Ht)).
    - exact (proj2 (H w1 st1 ltac:(lia) ltac:(lia) (past_quiet Hp Hq) Hd1 Ht1) ltac:(lia)
        (past_step (past_quiet Hp Hq)) stw st' Hs Hd Ht).
  Qed.

  (** A call that waits makes no event of its own until the response it waits for. *)
  Lemma meets_waiting tr w0 called typed k w :
    called <> i ->
    (forall w2 r spawns x, w0 <= w2 -> history w2 = Event_Respond a called r spawns -> gives N r x -> typed x ->
       meets tr (w2 + 1) (Running (k x)) w) ->
    meets tr w0 (Waiting called typed k) w.
  Proof.
    intros Hne H Hi Hp stw st' Hs Hd Ht.
    apply steps_waiting in Hs as [(-> & Hq & Hu) | (w2 & r & sp & x & Hw2 & Hq & Hu & He & Hg & Hty & Hs)].
    - exfalso. apply takes_waiting in Ht as (r & sp & x & He & _). rewrite He in Hd. destruct Hd as [_ Hd].
      exact (Hne Hd).
    - refine (H w2 r sp x ltac:(lia) He Hg Hty ltac:(lia) _ stw st' Hs Hd Ht).
      intros m Hm Hdm. destruct (Z.eq_dec m w2) as [-> | Hn].
      + exfalso. rewrite He in Hdm. destruct Hdm as [_ Hdm]. exact (Hne Hdm).
      + apply (past_quiet Hp Hq); [lia | exact Hdm].
  Qed.

  (** ** The rules *)

  (** What is claimed holds at every moment from `w0` on: nothing is left to go through. *)
  Lemma meets_from tr w0 st w : (forall k, w0 <= k -> claim k) -> meets tr w0 st w.
  Proof. intros H _ _ stw st' Hs _ _. apply H. exact (steps_later Hs). Qed.

  (** The program has its result: its event is the call's response, with that result. *)
  Lemma meets_ret tr w0 (x : res) w :
    (forall r, w0 <= w -> past w tr -> history w = Event_Respond a i r [] -> gives N r x -> claim w) ->
    meets tr w0 (Running (Ret x)) w.
  Proof.
    intros H Hi Hp stw st' Hs Hd Ht. pose proof (steps_later Hs) as Hle.
    apply step_ret in Hs as [[-> Hq] | (w1 & r & _ & _ & _ & _ & -> & _)].
    - apply takes_ret in Ht as (r & He & Hg & _). exact (H r Hle (past_quiet Hp Hq) He Hg).
    - destruct (takes_ended Ht).
  Qed.

  (** An operation on an object of the code. *)
  Lemma meets_op tr w0 X (o : Machine.op code obj X) (k : X -> program) w :
    ~ outside_call o -> ~ unsaid o ->
    (forall w1 x, w0 <= w1 -> past w1 tr -> op_event T known N a i o x (history w1) ->
       claim w1 /\ meets (w1 :: tr) (w1 + 1) (Running (k x)) w) ->
    meets tr w0 (Running (Vis o k)) w.
  Proof.
    intros Hext Hsaid H. apply meets_running. intros w1 st1 _ Hw1 Hp _ Ht.
    apply (takes_op_of Hext Hsaid) in Ht as (x & Hop & ->). exact (H w1 x Hw1 Hp Hop).
  Qed.

  (** A field of an object is read: the value read is of the field's type. *)
  Lemma meets_read tr w0 yh cls r f (k : exn + val -> program) w :
    names N yh (vref cls r) ->
    (forall w1 v y, w0 <= w1 -> past w1 tr -> names N y v -> field_typed T known cls f v ->
       history w1 = Event_Read a (Some i) yh (field_label T cls f) y ->
       claim w1 /\ meets (w1 :: tr) (w1 + 1) (Running (k (inr v))) w) ->
    meets tr w0 (Running (Vis (ObjGet r f) k)) w.
  Proof.
    intros Hyh H. apply meets_running. intros w1 st1 _ Hw1 Hp _ Ht.
    apply takes_read in Ht as (v & y & yo & Hyo & Hy & Hty & He & ->).
    destruct (read_place Hyh Hyo) as [-> Hcls]. rewrite Hcls in Hty, He. exact (H w1 v y Hw1 Hp Hy Hty He).
  Qed.

  (** A call of what is outside the code: made at `w1`, and responded to before `w2` with a result of the
      type its signature says. *)
  Lemma meets_called tr w0 m args (k : res -> program) w :
    (forall w1 ys, w0 <= w1 -> past w1 tr -> Forall2 (names N) ys args ->
       makes (history w1) (Invocation_mk m ys) ->
       claim w1 /\
       forall w2 r x, w1 < w2 -> done_inside history a i m ys w1 r w2 -> gives N r x -> returns known m x ->
         meets (w1 :: tr) w2 (Running (k x)) w) ->
    meets tr w0 (Running (Vis (ExtCall 0 m args) k)) w.
  Proof.
    intros H. apply meets_running. intros w1 st1 Hi Hw1 Hp _ Ht.
    apply takes_outside in Ht as (ys & Hys & [[He ->] | (r & sp & x & He & Hg & Hr & ->)]).
    - destruct (H w1 ys Hw1 Hp Hys (or_introl He)) as [Hc Hk]. split; [exact Hc |].
      apply meets_waiting; [lia |]. intros w2 r sp x Hw2 He2 Hg Hty.
      apply (Hk (w2 + 1) r x); [lia | | exact Hg | exact Hty].
      right. replace (w2 + 1 - 1) with w2 by lia. split; [exact He | split; [lia | exists sp; exact He2]].
    - destruct (H w1 ys Hw1 Hp Hys (or_intror (ex_intro _ r (ex_intro _ sp He)))) as [Hc Hk].
      split; [exact Hc |]. apply (Hk (w1 + 1) r x); [lia | | exact Hg | exact Hr].
      left. exists sp. split; [exact He | reflexivity].
  Qed.

  (** A call of a method of the code: made at `w1`, responded to at `w2`. *)
  Lemma meets_method tr w0 s on args (k : res -> program) m w :
    label_of s = m ->
    (forall w1 ys, w0 <= w1 -> past w1 tr -> Forall2 (names N) ys (receiver on ++ args) ->
       history w1 = Event_Invoke a (Some i) (Invocation_mk m ys) ->
       claim w1 /\
       forall w2 r spawns x, w1 < w2 -> history w2 = Event_Respond a w1 r spawns -> gives N r x ->
         meets (w1 :: tr) (w2 + 1) (Running (k x)) w) ->
    meets tr w0 (Running (Call (Method s) (VList (on :: args)) k)) w.
  Proof.
    intros <- H. apply meets_running. intros w1 st1 Hi Hw1 Hp _ Ht.
    apply takes_method_call in Ht as (ys & Hys & He & ->). destruct (H w1 ys Hw1 Hp Hys He) as [Hc Hk].
    split; [exact Hc |]. apply meets_waiting; [lia |]. intros w2 r sp x Hw2 He2 Hg _.
    exact (Hk w2 r sp x ltac:(lia) He2 Hg).
  Qed.

  (** A call of a function. *)
  Lemma meets_function tr w0 c arg (k : res -> program) w :
    (match c with Fn _ _ _ | Thunk _ _ => True | _ => False end) ->
    (forall w1 m y ys, w0 <= w1 -> past w1 tr -> called_as c arg m -> names N y (VCode c) ->
       Forall2 (names N) ys (arguments arg) ->
       history w1 = Event_Invoke a (Some i) (Invocation_mk m (y :: ys)) ->
       claim w1 /\
       forall w2 r spawns x, w1 < w2 -> history w2 = Event_Respond a w1 r spawns -> gives N r x ->
         meets (w1 :: tr) (w2 + 1) (Running (k x)) w) ->
    meets tr w0 (Running (Call c arg k)) w.
  Proof.
    intros Hc H. apply meets_running. intros w1 st1 Hi Hw1 Hp _ Ht.
    apply (takes_function_call Hc) in Ht as (m & y & ys & Hm & Hy & Hys & He & ->).
    destruct (H w1 m y ys Hw1 Hp Hm Hy Hys He) as [Hcl Hk]. split; [exact Hcl |].
    apply meets_waiting; [lia |]. intros w2 r sp x Hw2 He2 Hg _. exact (Hk w2 r sp x ltac:(lia) He2 Hg).
  Qed.

  (** ** A loop

      A turn of a loop is its body, and then the loop again or what follows it. What holds of the loop from
      each turn on (`J`) is shown of one turn, taking it of every later one. A turn makes an event. *)

  Lemma steps_quiet p w0 w : w0 <= w -> quiet w0 w -> steps w0 (Running p) w (Running p).
  Proof.
    intros Hle Hq. remember (Z.to_nat (w - w0)) as n eqn:En. revert w0 Hle Hq En.
    induction n as [| n IH]; intros w0 Hle Hq En.
    - replace w0 with w by lia. apply steps_here.
    - apply steps_other; [intros [Hd | []]; exact (Hq w0 ltac:(lia) Hd) |].
      apply IH; [lia | intros v Hv; apply Hq; lia | lia].
  Qed.

  Lemma steps_then w0 st0 w1 st1 w st : steps w0 st0 w1 st1 -> steps w1 st1 w st -> steps w0 st0 w st.
  Proof.
    induction 1 as [w' st' | w0 st0 w' st' Hn _ IH | w0 st0 st1' w' st' Hi Ht _ IH]; intros Hs.
    - exact Hs.
    - apply steps_other; [exact Hn | exact (IH Hs)].
    - eapply steps_own; [exact Hi | exact Ht | exact (IH Hs)].
  Qed.

  (** A program that takes each event another takes meets what the other meets. *)
  Lemma meets_alike tr w0 p q w :
    (forall v e st, takes v e (Running p) st -> takes v e (Running q) st) ->
    meets tr w0 (Running q) w -> meets tr w0 (Running p) w.
  Proof.
    intros Hpq H Hi Hp stw st' Hs Hd Ht. pose proof (steps_later Hs) as Hle.
    apply steps_running in Hs as [[-> Hq] | (w1 & st1 & Hw & Hq & Hd1 & Ht1 & Hs)].
    - exact (H Hi Hp (Running q) st' (steps_quiet q Hle Hq) Hd (Hpq _ _ _ Ht)).
    - refine (H Hi Hp stw st' (steps_then (@steps_quiet q w0 w1 ltac:(lia) Hq) _) Hd Ht).
      eapply steps_own; [left; exact Hd1 | exact (Hpq _ _ _ Ht1) | exact Hs].
  Qed.

  Lemma settles_turn S B (body : S -> Machine.P code obj (S + B)) s (k : B -> program) q :
    settles T (Iter body s k) q -> (match q with Iter _ _ _ => False | _ => True end) ->
    settles T (unfold_iter body s k) q.
  Proof.
    intros H Hn. remember (Iter body s k) as p eqn:E.
    destruct H as [p | S' B' body' s' k' p H | cls arg k' p H]; [subst p; destruct Hn | | discriminate E].
    injection E. intros Hk Hs Hb HB HS. subst S' B'.
    repeat match goal with E : existT _ _ _ = existT _ _ _ |- _ =>
      apply Dependent.EqdepTheory.inj_pair2 in E end.
    subst. exact H.
  Qed.

  Lemma takes_iter S B (body : S -> Machine.P code obj (S + B)) s (k : B -> program) w e st :
    takes w e (Running (Iter body s k)) st -> takes w e (Running (unfold_iter body s k)) st.
  Proof.
    intros H. inversion H; subst.
    - eapply takes_op; [apply settles_turn; [eassumption | exact I] | eassumption].
    - eapply takes_invoke; [apply settles_turn; [eassumption | exact I] | eassumption | reflexivity].
    - eapply takes_atomic; [apply settles_turn; [eassumption | exact I] | eassumption | reflexivity |
        eassumption | eassumption].
    - eapply takes_method; [apply settles_turn; [eassumption | exact I] | eassumption | reflexivity].
    - eapply takes_function; [apply settles_turn; [eassumption | exact I] | eassumption | eassumption |
        eassumption | eassumption | reflexivity].
    - eapply takes_end; [apply settles_turn; [eassumption | exact I] | reflexivity | eassumption].
    - eapply takes_unsaid; [apply settles_turn; [eassumption | exact I] | eassumption].
  Qed.

  Lemma meets_iter S B (body : S -> Machine.P code obj (S + B)) (k : B -> program)
      (J : list Z -> Z -> S -> Prop) w :
    (forall tr1 w1 s1, J tr1 w1 s1 ->
       (forall tr2 w2 s2, w1 < w2 -> J tr2 w2 s2 -> meets tr2 w2 (Running (Iter body s2 k)) w) ->
       meets tr1 w1 (Running (unfold_iter body s1 k)) w) ->
    forall tr0 w0 s0, J tr0 w0 s0 -> meets tr0 w0 (Running (Iter body s0 k)) w.
  Proof.
    intros H.
    assert (forall (n : nat) tr0 w0 s0, w - w0 < Z.of_nat n -> J tr0 w0 s0 ->
      meets tr0 w0 (Running (Iter body s0 k)) w) as Hn.
    { induction n as [| n IH]; intros tr0 w0 s0 Hlt HJ.
      - intros _ _ stw st' Hs. pose proof (steps_later Hs). lia.
      - apply meets_alike with (q := unfold_iter body s0 k); [intros v e st; apply takes_iter |].
        apply (H tr0 w0 s0 HJ). intros tr2 w2 s2 Hw2 HJ2. apply IH; [lia | exact HJ2]. }
    intros tr0 w0 s0. apply (Hn (Z.to_nat (w - w0 + 1))). lia.
  Qed.

  (** ** A call in an execution of the code *)

  Hypothesis conformed : conforms files T known N history.

  (** A call of a method of the code meets a claim at every event of its own, if its program does. *)
  Lemma method_meets inside s cls r d y ys :
    history i = Event_Invoke a inside (Invocation_mk (label_of s) (y :: ys)) ->
    names N y (vref cls r) -> impl T cls s = Some d ->
    (forall args w, Forall2 (names N) ys args -> passed known d args ->
       meets [] (i + 1) (Running (run T (Method s) (VList (vref cls r :: args)))) w) ->
    forall w, direct a i (history w) -> claim w.
  Proof.
    intros He Hy Hd H w Hdir.
    destruct (method_steps conformed s He Hy Hd) as (args & at_ & Hargs & Hp & Hlater & Hsteps & Htakes).
    pose proof (Hlater w Hdir) as Hw.
    refine (H args w Hargs Hp ltac:(lia) _ (at_ w) (at_ (w + 1)) (Hsteps w Hw) Hdir
      (Htakes w Hw (or_introl Hdir))).
    intros m Hm Hdm. pose proof (Hlater m Hdm). lia.
  Qed.

  (** A call of a function the code wrote. *)
  Lemma function_meets inside m c y ys :
    history i = Event_Invoke a inside (Invocation_mk m (y :: ys)) ->
    applies known m = true -> names N y (VCode c) -> written files c ->
    (forall args w, Forall2 (names N) ys args -> meets [] (i + 1) (Running (run T c (VList args))) w) ->
    forall w, direct a i (history w) -> claim w.
  Proof.
    intros He Hm Hy Hc H w Hdir.
    destruct (function_steps conformed He Hm Hy Hc) as (args & at_ & Hargs & Hlater & Hsteps & Htakes).
    pose proof (Hlater w Hdir) as Hw.
    refine (H args w Hargs ltac:(lia) _ (at_ w) (at_ (w + 1)) (Hsteps w Hw) Hdir (Htakes w Hw (or_introl Hdir))).
    intros k Hk Hdk. pose proof (Hlater k Hdk). lia.
  Qed.

End Logic.

Arguments method_meets {files T known N history a i} claim conformed {inside} s {cls r d y ys} _ _ _ _ w _.
Arguments function_meets {files T known N history a i} claim conformed {inside m c y ys} _ _ _ _ _ w _.

(** ** The values an event names, one by one *)

Lemma vals_none (R : Value -> val -> Prop) vs : Forall2 R [] vs -> vs = [].
Proof. intros H. inversion H. reflexivity. Qed.

Lemma vals_one (R : Value -> val -> Prop) y vs : Forall2 R [y] vs -> exists v, vs = [v] /\ R y v.
Proof. intros H. inversion H as [| ? v ? vs' Hy Hr]; subst. inversion Hr; subst. eauto. Qed.

Lemma args_none (R : Value -> val -> Prop) ys : Forall2 R ys [] -> ys = [].
Proof. intros H. inversion H. reflexivity. Qed.

Lemma args_one (R : Value -> val -> Prop) ys v : Forall2 R ys [v] -> exists y, ys = [y] /\ R y v.
Proof. intros H. inversion H as [| y ? ys' ? Hy Hr]; subst. inversion Hr; subst. eauto. Qed.

Lemma args_two (R : Value -> val -> Prop) ys v1 v2 :
  Forall2 R ys [v1; v2] -> exists y1 y2, ys = [y1; y2] /\ R y1 v1 /\ R y2 v2.
Proof.
  intros H. inversion H as [| y ? ys' ? Hy Hr]; subst. apply args_one in Hr as (y2 & -> & Hy2). eauto.
Qed.

(** ** Going through a program *)

(** A hypothesis taken apart: its definitions unfolded, each of its cases, each thing it says. *)
Ltac miss_open H :=
  try (progress autounfold with frflow_defs in H);
  lazymatch type of H with
  | _ /\ _ => let A := fresh in let B := fresh in destruct H as [A B]; miss_open A; miss_open B
  | _ \/ _ => destruct H as [H | H]; miss_open H
  | exists _, _ => let x := fresh in destruct H as [x H]; miss_open H
  | _ => idtac
  end.

(** What a type says of a value, in the hypothesis `H` that says the value is of it: nothing kept where it
    says nothing; that a call can be made on it, of a reference; the value itself, of a truth value or unit;
    each of none and an exception, of what is thrown. *)
Ltac typed H :=
  lazy beta iota zeta delta -[identity receiver held names Jdk.as_exn] in H;
  lazymatch type of H with
  | True => clear H
  | identity ?v => pose proof (identity_receiver v H)
  | held ?v = _ /\ receiver ?v = _ => let R := fresh "Hcalled_on" in destruct H as [H R]
  | ?v = _ \/ (exists _, Jdk.as_exn ?v = _) => destruct H as [H | [? H]]; [first [subst v | idtac] |]
  | exists _, ?v = _ => let b := fresh "b" in destruct H as [b H]; first [subst v | idtac]
  | ?v = VUnit => first [subst v | idtac]
  | _ => idtac
  end.

Ltac typed_all :=
  repeat match goal with
  | H : field_typed _ _ _ _ _ |- _ => typed H
  | H : returns _ _ (inr _) |- _ => typed H
  | H : returns _ _ (inl _) |- _ => clear H
  | H : called_as _ _ ?m |- _ => lazy in H; lazymatch type of H with True => clear H | _ = _ => subst m end
  | H : op_event _ _ _ _ _ _ _ _ |- _ =>
      cbn [op_event] in H; miss_open H; repeat match goal with E : ?x = inr _ |- _ => is_var x; subst x end
  end.

(** What follows a step, set aside under a name: dropped once nothing speaks of it. *)
Ltac aside_clear := repeat match goal with K := _ |- _ => clear K end.

(** What the program asks first that the walk can settle itself (as `walk_answer`), in the goal. *)
Ltac meets_answer :=
  match goal with
  | |- context [implemented ?T' ?v ?s] =>
      let d := eval lazy in (implemented T' v s) in
      lazymatch d with
      | Some _ => change (implemented T' v s) with d
      | None => change (implemented T' v s) with d
      | _ =>
          let E := fresh in
          assert (E : unimplemented T' s = true) by (vm_compute; reflexivity);
          rewrite (implemented_none T' s v E); clear E
      end
  | |- context [held ?v] =>
      first
        [ rewrite (held_identity v ltac:(assumption))
        | match goal with E : held v = _ |- _ => rewrite E end
        | let d := eval lazy in (held v) in
          lazymatch d with
          | Ret _ => change (held v) with d
          | Vis _ _ => change (held v) with d
          | Call _ _ _ => change (held v) with d
          end ]
  | |- context [Jdk.as_exn ?v] =>
      first
        [ match goal with E : Jdk.as_exn v = _ |- _ => rewrite E end
        | let d := eval lazy in (Jdk.as_exn v) in
          lazymatch d with
          | Some _ => change (Jdk.as_exn v) with d
          | None => change (Jdk.as_exn v) with d
          end ]
  | |- context [equal ?T' ?a ?b] =>
      unify b vnull;
      rewrite (@equal_null T' a ltac:(first [assumption | left; reflexivity | right; eexists; eassumption]))
  | |- context [equal ?T' ?a ?b] =>
      let E := fresh in
      assert (E : unnamed T' "equals" = true) by (vm_compute; reflexivity);
      rewrite (equal_identity T' a b ltac:(assumption) ltac:(assumption) E); clear E
  | |- context [val_eqb ?a ?b] =>
      first
        [ unify a b; change (val_eqb a b) with (val_eqb a a); rewrite (val_eqb_refl a)
        | let d := eval lazy in (val_eqb a b) in
          lazymatch d with
          | true => change (val_eqb a b) with true
          | false => change (val_eqb a b) with false
          end ]
  end.

(** A result or a truth value the program `p` goes by, not known: each way it can be. *)
Ltac meets_each p :=
  match p with
  | context [match ?x with _ => _ end] =>
      is_var x;
      let t := type of x in
      lazymatch t with
      | bool => idtac
      | res => idtac
      | Machine.res _ _ => idtac
      | sum _ _ => idtac
      end;
      destruct x
  | context [val_eqb ?a ?b] => let E := fresh "E" in destruct (val_eqb a b) eqn:E
  end.

(** The program of the goal with its next step computed: its first operation, call or result, what follows
    it set aside under a name. A result or a truth value not known is taken each way it can be. *)
Ltac meets_head :=
  typed_all;
  lazymatch goal with
  | |- meets ?T ?C ?N ?h ?a ?i ?G ?tr ?w0 (Running ?p) ?w =>
      let p' := eval lazy head beta iota zeta delta -[implemented held equal val_eqb Jdk.as_exn] in p in
      lazymatch p' with
      | Vis ?o ?k =>
          let o' := eval lazy beta iota zeta delta -[receiver] in o in
          let K := fresh "K" in
          pose (K := k); change (meets T C N h a i G tr w0 (Running (Vis o' K)) w); aside_clear;
          repeat match goal with E : receiver ?v = _ |- _ => rewrite E end; cbn [app]
      | Call ?c ?arg ?k =>
          let c' := eval lazy in c in
          let arg' := eval lazy in arg in
          let K := fresh "K" in
          pose (K := k); change (meets T C N h a i G tr w0 (Running (Call c' arg' K)) w); aside_clear
      | Ret ?x => let x' := eval lazy in x in change (meets T C N h a i G tr w0 (Running (Ret x')) w); aside_clear
      | Iter ?body ?s ?k =>
          first
            [ is_var body; is_var k; change (meets T C N h a i G tr w0 (Running (Iter body s k)) w)
            | let B := fresh "B" in
              let K := fresh "K" in
              pose (B := body); pose (K := k); change (meets T C N h a i G tr w0 (Running (Iter B s K)) w) ];
          aside_clear
      | _ =>
          change (meets T C N h a i G tr w0 (Running p') w); aside_clear;
          first [meets_answer; meets_head | meets_each p'; meets_head | idtac]
      end
  end.

(** The rule of what the program does next. *)
Ltac step_rule :=
  lazymatch goal with
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Vis (ObjGet _ _) _)) _ => eapply meets_read; [eassumption |]
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Vis (ExtCall 0 _ _) _)) _ => apply meets_called
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Vis _ _)) _ =>
      apply meets_op; [intros [] | intros [] |]
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Call (Method _) _ _)) _ => eapply meets_method; [lazy; reflexivity |]
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Call _ _ _)) _ => apply meets_function; [exact I |]
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Ret _)) _ => apply meets_ret
  end.

Ltac step := meets_head; step_rule.

(** ** An event the claim says nothing of *)

(** A response that is not the result. *)
Ltac miss_given :=
  match goal with
  | G : gives _ (Response_Returned _) (inl _) |- _ => destruct G
  | G : gives _ (Response_Threw _) (inr _) |- _ => destruct G
  end.

(** Two things said of the event of one moment that cannot both be. *)
Ltac miss_now :=
  first
    [ congruence
    | match goal with
      | M : ?h ?w = _, E : ?h ?w = _ |- _ =>
          rewrite E in M; first [discriminate M | injection M; intros; subst; miss_given]
      | M : ?h ?w = _, E : makes _ _ (?h ?w) _ |- _ =>
          destruct E as [E | (? & ? & E)]; rewrite E in M;
          first [discriminate M | injection M; intros; subst; first [congruence | miss_given]]
      | M : ?h ?w = _, E : op_event _ _ _ _ _ _ _ (?h ?w) |- _ =>
          cbn [op_event] in E; miss_open E; congruence
      end ].

(** What the claim takes is of an event of the call's own before the moment the walk is at: that event is one of
    those gone through, and is none of them. *)
Ltac miss_past :=
  match goal with
  | P : past _ _ _ ?k ?tr, M : ?h ?m = _ |- _ =>
      let Hin := fresh "Hin" in
      assert (Hin : In m tr) by (apply P; [lia | rewrite M; cbn; auto]);
      cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]); [.. | destruct Hin]; miss_now
  end.

Ltac miss_end := first [miss_now | miss_past].

(** The claim holds at an event because what it is of is another event: what the claim takes of the event is
    taken apart, and cannot be with what the rule says the event is. *)
Ltac miss_goal :=
  lazymatch goal with
  | |- _ /\ _ => split; miss_goal
  | |- ~ _ => let M := fresh "M" in intro M; miss_open M; miss_goal
  | |- forall _, _ => let M := fresh "M" in intro M; miss_open M; miss_goal
  | |- _ => solve [miss_end]
  end.

Ltac miss := aside_clear; cbv beta; miss_goal.

(** The rule of what the program does next, at an event the claim says nothing of; then on. A loop is left
    as it is, for `meets_iter`. *)
Ltac pass :=
  meets_head;
  lazymatch goal with
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Ret _)) _ => apply meets_ret; intros ? ? ? ? ?; miss
  | |- meets _ _ _ _ _ _ _ _ _ (Running (Iter _ _ _)) _ => idtac
  | |- _ => step_rule; intros; typed_all; (split; [miss | intros; typed_all])
  end.
