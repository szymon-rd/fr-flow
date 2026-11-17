(** An execution written out, and shown to be one of the code.

    That a model's assumptions can hold together is shown by an execution that meets them. The one in which
    nothing happens meets most assumptions by saying nothing; it shows little. Here is what it takes to write
    out an execution in which things happen, event by event, and to show that it is one of the code:

    - `history_of`: the execution whose events are those of a list, in order, from the moment 0; `among` says
      where an event of it is, one case for each event of the list;
    - `naming_of`: which value of the code each reference of the execution is, from a table of them;
    - `goes`: a call follows its program, shown one event of its own after another (`goes_step`), up to its
      response or to where it waits for good (`goes_idle`); `follows_of` makes of it what `Conforms` asks. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia Classical PropExtensionality.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Code.Walk.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ** An execution written out *)

(** The events of the list, one at each moment from 0; nothing happens before, nor after. *)
Definition history_of (events : list Event) (w : Z) : Event :=
  if w <? 0 then Event_Stutter else nth (Z.to_nat w) events Event_Stutter.

(** The event `e` is the one of the list at the moment `w`, the list beginning at the moment `k`. *)
Fixpoint among (k : Z) (events : list Event) (w : Z) (e : Event) : Prop :=
  match events with
  | [] => False
  | x :: rest => (w = k /\ e = x) \/ among (k + 1) rest w e
  end.

Lemma nth_among (events : list Event) (k : Z) (n : nat) :
  nth n events Event_Stutter = Event_Stutter \/ among k events (k + Z.of_nat n) (nth n events Event_Stutter).
Proof.
  revert k n. induction events as [| x rest IH]; intros k n.
  - left. destruct n; reflexivity.
  - destruct n as [| n].
    + right. left. split; [cbn; lia | reflexivity].
    + destruct (IH (k + 1) n) as [E | E]; [left; exact E | right; right].
      replace (k + Z.of_nat (S n)) with (k + 1 + Z.of_nat n) by lia. exact E.
Qed.

(** What happens at a moment is nothing, or one of the events written, at its moment. *)
Lemma history_among (events : list Event) (w : Z) :
  history_of events w = Event_Stutter \/ among 0 events w (history_of events w).
Proof.
  unfold history_of. destruct (w <? 0) eqn:E; [left; reflexivity |]. apply Z.ltb_ge in E.
  destruct (nth_among events 0 (Z.to_nat w)) as [H | H]; [left; exact H | right].
  replace (0 + Z.of_nat (Z.to_nat w)) with w in H by lia. exact H.
Qed.

(** ** Which value of the code each reference is *)

Fixpoint ref_at (refs : list (Z * val)) (n : Z) : option val :=
  match refs with
  | [] => None
  | (m, v) :: rest => if Z.eqb m n then Some v else ref_at rest n
  end.

(** A reference is the value the table gives it; any other value is what it is in every execution. *)
Definition named_by (refs : list (Z * val)) (x : Value) : option val :=
  match x with
  | Value_Reference n => ref_at refs n
  | other => plain_val other
  end.

(** The class of an exception of the JDK that is known by its class alone. *)
Definition exn_class (e : exn) : option string :=
  match e with
  | InterruptedException => Some "java.lang.InterruptedException"
  | IllegalStateException => Some "java.lang.IllegalStateException"
  | IllegalThreadStateException => Some "java.lang.IllegalThreadStateException"
  | NullPointerException => Some "java.lang.NullPointerException"
  | NoSuchElementException => Some "java.util.NoSuchElementException"
  | Machine.Other cls => match made_exn cls with Machine.Other _ => Some cls | _ => None end
  | _ => None
  end.

Lemma exn_class_made (e : exn) (cls : string) : exn_class e = Some cls -> made_exn cls = e.
Proof.
  destruct e; cbn; try discriminate; try (intros H; injection H as <-; reflexivity).
  destruct (made_exn class) eqn:E; try discriminate. intros H. injection H as <-.
  unfold made_exn in *.
  repeat match type of E with context [String.eqb ?x ?y] => destruct (String.eqb x y); try discriminate E end.
  reflexivity.
Qed.

Lemma made_exn_class (cls : string) : exn_class (made_exn cls) = Some cls.
Proof.
  unfold made_exn.
  repeat match goal with |- context [String.eqb ?x ?y] => destruct (String.eqb_spec x y) as [-> | ?]; [reflexivity |] end.
  cbn. unfold made_exn.
  repeat match goal with |- context [String.eqb ?x ?y] => destruct (String.eqb_spec x y) as [-> | ?]; [contradiction |] end.
  reflexivity.
Qed.

(** The value of an execution that a value of the code is in every execution: unit, a truth value, a number, a
    text, no object, an exception of the JDK by its class. None for any other value: a reference names it. *)
Definition plain_of (v : val) : option Value :=
  match v with
  | VUnit => Some Value_Unit_
  | VBool b => Some (Value_Bool_ (b = true))
  | VObj (Int z) => Some (Value_Int_ z)
  | VObj (Str s) => Some (Value_Str s)
  | VObj Null => Some Value_Null
  | VExn e => option_map Value_Thrown (exn_class e)
  | _ => None
  end.

Lemma plain_of_val (v : val) (x : Value) : plain_of v = Some x -> plain_val x = Some v.
Proof.
  destruct v as [| b | | e | o | |]; cbn; try discriminate.
  - intros H. injection H as <-. reflexivity.
  - intros H. injection H as <-. exact (of_bool plain_naming b).
  - destruct (exn_class e) as [cls |] eqn:E; cbn; [| discriminate]. intros H. injection H as <-. cbn.
    rewrite (exn_class_made e cls E). reflexivity.
  - destruct o; try discriminate; intros H; injection H as <-; reflexivity.
Qed.

Lemma plain_val_of (x : Value) (v : val) : plain_val x = Some v -> plain_of v <> None.
Proof.
  destruct x as [| P | z | s | r | cls |]; cbn; try discriminate; try (intros H; injection H as <-; discriminate).
  - repeat destruct (excluded_middle_informative _); try discriminate; intros H; injection H as <-; discriminate.
  - intros H. injection H as <-. cbn. rewrite made_exn_class. discriminate.
Qed.

(** A value a reference can be: one that is no value of every execution. *)
Definition referred (v : val) : bool := match plain_of v with None => true | Some _ => false end.

(** The table names each value once, by one reference, and only values a reference can be. *)
Fixpoint well_named (refs : list (Z * val)) : bool :=
  match refs with
  | [] => true
  | (n, v) :: rest =>
      referred v && forallb (fun p => negb (Z.eqb (fst p) n) && negb (val_eqb (snd p) v)) rest &&
      well_named rest
  end.

(** Each object of the code the table names is of the class its place has. *)
Definition placed (places : nat -> string) (refs : list (Z * val)) : bool :=
  forallb (fun p => match snd p with VObj (Ref c r) => String.eqb (places r) c | _ => true end) refs.

Lemma ref_at_in refs n v : ref_at refs n = Some v -> In (n, v) refs.
Proof.
  induction refs as [| [m u] rest IH]; cbn; [discriminate |].
  destruct (Z.eqb_spec m n) as [-> | _]; [intros E; injection E as ->; left; reflexivity | right; auto].
Qed.

Lemma ref_at_one refs n m v : well_named refs = true -> ref_at refs n = Some v -> ref_at refs m = Some v -> n = m.
Proof.
  induction refs as [| [k u] rest IH]; cbn; [discriminate |]. intros Hw Hn Hm.
  apply andb_true_iff in Hw as [Hw Hrest]. apply andb_true_iff in Hw as [_ Hfresh].
  assert (forall j, ref_at rest j = Some u -> False) as Hnot.
  { intros j Hj. apply ref_at_in in Hj. pose proof (proj1 (forallb_forall _ _) Hfresh _ Hj) as Hp. cbn in Hp.
    apply andb_true_iff in Hp as [_ Hp]. apply negb_true_iff in Hp. rewrite (proj2 (val_eqb_eq u u) eq_refl) in Hp.
    discriminate Hp. }
  destruct (Z.eqb_spec k n) as [Ekn | Hkn], (Z.eqb_spec k m) as [Ekm | Hkm].
  - congruence.
  - injection Hn as ->. destruct (Hnot m Hm).
  - injection Hm as ->. destruct (Hnot n Hn).
  - exact (IH Hrest Hn Hm).
Qed.

Lemma ref_at_referred refs n v : well_named refs = true -> ref_at refs n = Some v -> referred v = true.
Proof.
  induction refs as [| [k u] rest IH]; cbn; [discriminate |]. intros Hw Hn.
  apply andb_true_iff in Hw as [Hw Hrest]. apply andb_true_iff in Hw as [Hu _].
  destruct (Z.eqb_spec k n) as [_ | _]; [injection Hn as <-; exact Hu | exact (IH Hrest Hn)].
Qed.

Lemma plain_not_referred x v : plain_val x = Some v -> referred v = false.
Proof. intros H. unfold referred. destruct (plain_of v) eqn:E; [reflexivity | destruct (plain_val_of x v H E)]. Qed.

Definition naming_of (refs : list (Z * val)) (places : nat -> string) :
  well_named refs = true -> placed places refs = true -> naming.
Proof.
  intros Hw Hp.
  refine (Naming (named_by refs) places (of_unit plain_naming) (of_bool plain_naming) (of_int plain_naming)
    (of_str plain_naming) (of_thrown plain_naming) (of_null plain_naming) _ _).
  - intros x y v Hx Hy.
    destruct x as [| P | z | s | n | cls |], y as [| Q | z' | s' | m | cls' |];
      try exact (one_name plain_naming _ _ _ Hx Hy);
      try (cbn [named_by] in Hx, Hy;
        first [ rewrite (ref_at_one refs n m v Hw Hx Hy); reflexivity
              | pose proof (ref_at_referred refs _ v Hw Hx) as R;
                rewrite (plain_not_referred _ v Hy) in R; discriminate R
              | pose proof (ref_at_referred refs _ v Hw Hy) as R;
                rewrite (plain_not_referred _ v Hx) in R; discriminate R ]).
  - intros x c r Hx. destruct x as [| P | z | s | n | cls |];
      try (pose proof (plain_not_referred _ _ Hx) as R; discriminate R).
    cbn [named_by] in Hx. apply ref_at_in in Hx.
    pose proof (proj1 (forallb_forall _ _) Hp _ Hx) as Hc. cbn in Hc. apply String.eqb_eq in Hc. exact Hc.
Defined.

(** ** A call that follows its program, one event of its own after another *)

Section Goes.

  Variable T : table.
  Variable known : classes.
  Variable N : naming.
  Variable history : Z -> Event.
  Variable a : Value.
  Variable i : Z.

  (** From `w0` the call is at the stage `st`: it stays there for good, making no event of its own; or its
      next event, at `w1`, takes it to a stage it goes on from. *)
  Inductive goes : Z -> stage -> Prop :=
    | goes_idle w0 st : (forall w, w0 <= w -> ~ its st a i (history w)) -> goes w0 st
    | goes_step w0 st w1 st1 :
        w0 <= w1 -> (forall w, w0 <= w < w1 -> ~ its st a i (history w)) ->
        its st a i (history w1) -> takes T known N a i w1 (history w1) st st1 ->
        goes (w1 + 1) st1 -> goes w0 st.

  Lemma goes_staged w0 st :
    goes w0 st -> exists at_ : Z -> stage, at_ w0 = st /\
      forall w, w0 <= w ->
        (its (at_ w) a i (history w) -> takes T known N a i w (history w) (at_ w) (at_ (w + 1))) /\
        (~ its (at_ w) a i (history w) -> at_ (w + 1) = at_ w).
  Proof.
    induction 1 as [w0 st Hnone | w0 st w1 st1 Hle Hquiet Hits Htakes _ (at1 & H1 & Hrest)].
    - exists (fun _ => st). split; [reflexivity |]. intros w Hw.
      split; [intros H; destruct (Hnone w Hw H) | reflexivity].
    - exists (fun w => if Z.leb w w1 then st else at1 w). split.
      { rewrite (proj2 (Z.leb_le w0 w1) Hle). reflexivity. }
      intros w Hw. destruct (Z_lt_le_dec w w1) as [Hlt | Hge].
      + rewrite (proj2 (Z.leb_le w w1) ltac:(lia)), (proj2 (Z.leb_le (w + 1) w1) ltac:(lia)).
        split; [intros H; destruct (Hquiet w ltac:(lia) H) | reflexivity].
      + destruct (Z.eq_dec w w1) as [-> | Hne].
        * rewrite (proj2 (Z.leb_le w1 w1) ltac:(lia)), (proj2 (Z.leb_gt (w1 + 1) w1) ltac:(lia)), H1.
          split; [intros _; exact Htakes | intros Hn; destruct (Hn Hits)].
        * rewrite (proj2 (Z.leb_gt w w1) ltac:(lia)), (proj2 (Z.leb_gt (w + 1) w1) ltac:(lia)).
          exact (Hrest w ltac:(lia)).
  Qed.

  (** A call that makes no event of its own before it is made nor after it is responded to, and goes on from
      its program, follows it. *)
  Lemma follows_of (p : program) :
    (forall w, w <= i -> ~ direct a i (history w)) ->
    (forall k w r spawns, history k = Event_Respond a i r spawns -> k < w -> ~ direct a i (history w)) ->
    goes (i + 1) (Running p) -> follows T known N history a i p.
  Proof.
    intros Hbefore Hafter Hgoes. destruct (goes_staged (i + 1) (Running p) Hgoes) as (at_ & H0 & Hall).
    split; [exact Hbefore | split; [exact Hafter |]]. exists at_. split; [exact H0 |].
    intros w Hw. apply Hall. lia.
  Qed.

End Goes.

(** ** One step, by computing

    The stage a call is at holds its whole program; an event of its own is told from the stage's kind alone. *)

(** The response a call waits for. *)
Definition answered (a : Value) (called : Z) (e : Event) : Prop :=
  match e with Event_Respond b invoked _ _ => b = a /\ invoked = called | _ => False end.

Lemma its_running (p : program) a i e : its (Running p) a i e -> direct a i e.
Proof. intros [H | H]; [exact H | destruct H]. Qed.

Lemma its_ended a i e : its Ended a i e -> direct a i e.
Proof. intros [H | H]; [exact H | destruct H]. Qed.

Lemma its_waiting called (typed : res -> Prop) (k : res -> program) a i e :
  its (Waiting called typed k) a i e -> direct a i e \/ answered a called e.
Proof. intros [H | H]; [left; exact H | right; destruct e; exact H]. Qed.

Lemma takes_returned T known N a i w e p m args (k : res -> program) ys y v spawns :
  settles T p (Vis (ExtCall 0 m args) k) ->
  e = Event_Atomic a (Some i) (Invocation_mk m ys) (Response_Returned y) spawns ->
  Forall2 (names N) ys args -> names N y v -> returns known m (inr v) ->
  takes T known N a i w e (Running p) (Running (k (inr v))).
Proof. intros Hs He Hys Hy Hr. eapply takes_atomic; [exact Hs | exact Hys | exact He | exact Hy | exact Hr]. Qed.

Lemma takes_gave T known N a i w e called (typed : res -> Prop) (k : res -> program) y v spawns :
  e = Event_Respond a called (Response_Returned y) spawns -> names N y v -> typed (inr v) ->
  takes T known N a i w e (Waiting called typed k) (Running (k (inr v))).
Proof. intros He Hy Ht. eapply takes_response; [exact He | exact Hy | exact Ht]. Qed.

(** What a program does next, past what makes no event. *)
Ltac settle :=
  lazymatch goal with
  | |- settles ?T ?p ?q =>
      let p' := eval lazy head beta iota zeta delta in p in
      change (settles T p' q);
      lazymatch p' with
      | Iter _ _ _ => apply settles_iter; settle
      | Call (Init _) _ _ => apply settles_init; settle
      | Call (Thunk _ _) (VList []) _ => apply settles_forced; settle
      | _ => apply settled
      end
  end.

(** A fact about values written out: by computing. *)
Ltac fact :=
  first
    [ reflexivity
    | exact I
    | exact (of_bool _ _)
    | (unfold names; reflexivity)
    | (apply Forall2_nil)
    | (apply Forall2_cons; [fact | fact])
    | (split; [fact | fact])
    | (eexists; fact)
    | (left; fact)
    | (right; fact)
    | (intros ? ? E; discriminate E)
    | (progress lazy; fact) ].

(** The event at a moment written out is the one the program's next step makes. *)
Ltac take :=
  lazymatch goal with
  | |- takes _ _ _ _ _ _ (history_of ?evs ?n) _ _ =>
      let e := eval lazy in (history_of evs n) in change (history_of evs n) with e
  end;
  first
    [ solve [eapply takes_gave; [reflexivity | fact | fact]]
    | solve [eapply takes_returned; [settle | reflexivity | fact | fact | fact]]
    | solve [eapply takes_op; [settle | cbn [op_event]; repeat eexists; repeat split; revgoals;
        try solve [reflexivity | unfold names; reflexivity | unfold at_place, names; reflexivity
                  | exact (of_bool _ _)];
        fact]]
    | solve [eapply takes_end; [settle | reflexivity | fact]]
    | solve [eapply takes_method; [settle | ..]; revgoals; [reflexivity | fact]]
    | solve [eapply takes_invoke; [settle | ..]; revgoals; [reflexivity | fact]]
    | solve [eapply takes_function; [settle | ..]; revgoals; [reflexivity | fact | fact | fact | fact]] ].

(** Two moments written out are not in the order said. *)
Ltac out_of_order :=
  match goal with
  | H : _ /\ _ |- _ => destruct H; out_of_order
  | H : (_ <= _)%Z |- _ => exact (False_ind _ (H eq_refl))
  | H : (_ < _)%Z |- _ => (vm_compute in H; discriminate H)
  end.

(** No event written out, at the moments asked of, is the call's own. *)
Ltac quiet :=
  let w := fresh "w" in let Hw := fresh "Hw" in let Hits := fresh "Hits" in
  let E := fresh "E" in let e := fresh "e" in
  intros w Hw Hits;
  lazymatch type of Hits with
  | its (Running _) _ _ _ => apply its_running in Hits
  | its Ended _ _ _ => apply its_ended in Hits
  | its (Waiting _ _ _) _ _ _ => apply its_waiting in Hits
  end;
  lazymatch type of Hits with
  | context [history_of ?evs w] =>
      destruct (history_among evs w) as [E | E]; revert Hits E; generalize (history_of evs w); intros e Hits E;
      [ rewrite E in Hits; cbn in Hits; tauto
      | lazy in E;
        repeat (destruct E as [[-> ->] | E];
          [first [out_of_order | cbn in Hits; solve [intuition (first [congruence | lia])]] |]);
        exact (False_ind _ E) ]
  end.

(** The call's next event is the one at the moment `n`; `answer_at` where it is the response of the call it
    waits for. Whether the event is the call's is looked at first: it is what fails where it is not. *)
Ltac own_at n :=
  eapply goes_step with (w1 := n); only 3: (left; hnf; split; reflexivity); [lia | quiet | take |].
Ltac answer_at n :=
  eapply goes_step with (w1 := n); only 3: (right; hnf; split; reflexivity); [lia | quiet | take |].
Ltac rests := solve [apply goes_idle; quiet].

(** A call goes on from its program to where it rests: each next event of its own is found, from the moment it
    has come to, and taken. *)
Ltac step_from n fuel :=
  lazymatch fuel with
  | O => fail "no next event of the call"
  | S ?f => first [own_at n | answer_at n | let n' := eval lazy in (n + 1) in step_from n' f]
  end.
Ltac go :=
  repeat (lazymatch goal with
    | |- goes _ _ _ _ _ _ ?w0 _ => first [rests | let w := eval lazy in w0 in step_from w 400%nat]
    end).

(** ** Which class, and which method, a call is of *)

Lemma sym_eqb_eq (a b : sym) : sym_eqb a b = true -> a = b.
Proof.
  destruct a as [| o n g | n k], b as [| o' n' g' | n' k']; cbn; try discriminate; try reflexivity.
  - intros H. apply andb_true_iff in H as [H Ho]. apply andb_true_iff in H as [Hn Hg].
    apply String.eqb_eq in Ho, Hn, Hg. subst. reflexivity.
  - intros H. apply andb_true_iff in H as [Hn Hk]. apply String.eqb_eq in Hn. apply Nat.eqb_eq in Hk.
    subst. reflexivity.
Qed.

Lemma assoc_in {A : Type} (xs : list (string * A)) (k : string) (x : A) : assoc xs k = Some x -> In (k, x) xs.
Proof.
  induction xs as [| [k' y] rest IH]; cbn; [discriminate |].
  destruct (String.eqb_spec k' k) as [-> | _]; [intros E; injection E as ->; left; reflexivity | right; auto].
Qed.

(** A class of the code is one of those its files define. *)
Lemma class_in_among (T : table) (name : string) (c : tree) :
  class_in T name = Some c -> In (name, c) (classes_of T).
Proof.
  induction T as [classes members lines modules | T1 IH1 T2 IH2]; cbn.
  - apply assoc_in.
  - destruct (class_in T1 name) as [c1 |] eqn:E.
    + intros H. injection H as <-. apply in_or_app. left. exact (IH1 eq_refl).
    + intros H. apply in_or_app. right. exact (IH2 H).
Qed.

Lemma class_of_among (T : table) (name : string) (c : tree) :
  class_of T name = Some c -> In (name, c) (classes_of T).
Proof. unfold class_of. destruct (foreign name); [discriminate | apply class_in_among]. Qed.

Lemma first_some_found {A B : Type} (f : A -> option B) (xs : list A) (b : B) :
  first_some f xs = Some b -> exists x, In x xs /\ f x = Some b.
Proof.
  induction xs as [| x rest IH]; cbn; [discriminate |].
  destruct (f x) as [y |] eqn:E.
  - intros H. injection H as ->. exists x. split; [left; reflexivity | exact E].
  - intros H. destruct (IH H) as (x' & Hin & Hx). exists x'. split; [right; exact Hin | exact Hx].
Qed.

(** The body a call runs is a method, with a body, of a class the object's class inherits from: the method
    called, or one that overrides it. *)
Lemma impl_found (T : table) (cls : string) (s : sym) (d : tree) :
  impl T cls s = Some d ->
  exists name c, In name (own T cls) /\ class_of T name = Some c /\ In d (class_body c) /\
    match d with
    | DefDef s' _ _ _ (Some _) overridden => s' = s \/ In s overridden
    | _ => False
    end.
Proof.
  unfold impl. intros H. apply first_some_found in H as (name & Hname & H).
  destruct (class_of T name) as [c |] eqn:Ec; [| discriminate H].
  exists name, c. split; [exact Hname | split; [exact Ec |]].
  unfold own_impl in H. apply find_some in H as [Hin Hd]. split; [exact Hin |].
  destruct d; try discriminate Hd.
  match type of Hd with match ?b with _ => _ end = true => destruct b; [| discriminate Hd] end.
  apply orb_true_iff in Hd as [Hd | Hd]; [left; exact (sym_eqb_eq _ _ Hd) | right].
  unfold known in Hd. apply existsb_exists in Hd as (x & Hx & Ex). apply sym_eqb_eq in Ex. subst x. exact Hx.
Qed.

(** ** Which methods a label can be of

    A call of the execution is known by its label. Which methods of the code that can be is found by looking
    through the code: the methods with a body that an object of the class has, or that override one, and are
    labelled so. *)

(** What the classes an object of class `cls` is of declare. *)
Definition bodies (T : table) (cls : string) : list tree :=
  flat_map (fun name => match class_of T name with Some c => class_body c | None => [] end) (own T cls).

(** The methods a definition gives a body to, labelled `m`. *)
Definition labelled (m : string) (d : tree) : list sym :=
  match d with
  | DefDef s _ _ _ (Some _) overridden => filter (fun s' => String.eqb (label_of s') m) (s :: overridden)
  | _ => []
  end.

Lemma impl_labelled (T : table) (cls : string) (s : sym) (d : tree) :
  impl T cls s = Some d -> In s (flat_map (labelled (label_of s)) (bodies T cls)).
Proof.
  intros H. destruct (impl_found T cls s d H) as (name & c & Hname & Hc & Hd & Hs).
  apply in_flat_map. exists d. split.
  - unfold bodies. apply in_flat_map. exists name. split; [exact Hname | rewrite Hc; exact Hd].
  - destruct d; try destruct Hs.
    match goal with |- In _ (labelled _ (DefDef _ _ _ _ ?b _)) => destruct b end; [| destruct Hs].
    cbn [labelled]. apply filter_In. split; [| apply String.eqb_refl].
    destruct Hs as [-> | Hs]; [left; reflexivity | right; exact Hs].
Qed.

(** The classes of the code that are an object alone of its class. *)
Definition modules_of (T : table) : list string :=
  map fst (filter (fun nc => is_module (snd nc)) (classes_of T)).

Lemma module_labelled (T : table) (owner name signature : string) (c d : tree) :
  class_of T owner = Some c -> is_module c = true -> impl T owner (Member owner name signature) = Some d ->
  In (Member owner name signature)
    (flat_map (fun o => flat_map (labelled (label owner name signature)) (bodies T o)) (modules_of T)).
Proof.
  intros Hc Hm Hd. apply in_flat_map. exists owner. split.
  - unfold modules_of. apply in_map_iff. exists (owner, c). split; [reflexivity |].
    apply filter_In. split; [exact (class_of_among T owner c Hc) | exact Hm].
  - exact (impl_labelled T owner (Member owner name signature) d Hd).
Qed.

Lemma prefix_app (a b c : string) : String.prefix b c = true -> String.prefix (a ++ b) (a ++ c) = true.
Proof.
  intros H. induction a as [| x a IH]; [exact H |]. cbn. destruct (Ascii.ascii_dec x x) as [_ | N]; [exact IH |].
  destruct (N eq_refl).
Qed.

(** The classes of the code whose constructor a label can be of. *)
Lemma constructor_labelled (T : table) (cls signature : string) (c : tree) :
  class_of T cls = Some c ->
  In cls (filter (fun o => String.prefix (o ++ " <init> ") (label cls "<init>" signature)) (map fst (classes_of T))).
Proof.
  intros Hc. apply filter_In. split.
  - apply in_map_iff. exists (cls, c). split; [reflexivity | exact (class_of_among T cls c Hc)].
  - unfold label. apply prefix_app. cbn. apply String.prefix_correct. destruct signature; reflexivity.
Qed.

(** ** Each event of an execution written out *)

(** The event at a moment: one case for each event written that can be the one said. *)
Ltac scan H :=
  lazymatch type of H with
  | history_of ?evs ?w = _ =>
      let E := fresh "E" in let e := fresh "e" in let m := fresh "m" in let Em := fresh "Em" in
      destruct (history_among evs w) as [E | E]; revert H E; generalize (history_of evs w); intros e H E;
      [ rewrite E in H; discriminate H
      | remember w as m eqn:Em in E; lazy in E;
        repeat (let Ew := fresh "Ew" in
          destruct E as [[Ew ->] | E]; [first [discriminate H | subst m; first [subst w | idtac]] |]);
        try destruct E ]
  end.

(** What two responses, or two truth values, said to be the same tell. *)
Ltac learn :=
  repeat match goal with
    | H : Response_Returned _ = Response_Returned _ |- _ => injection H as H
    | H : Response_Threw _ = Response_Threw _ |- _ => injection H as H
    | H : Value_Bool_ _ = Value_Bool_ _ |- _ => injection H as H
    end;
  subst.

(** What is said to be in the execution, taken apart down to the events it speaks of: one case for each way
    the events written out make it so, with what that tells. *)
Ltac break H :=
  lazymatch type of H with
  | _ \/ _ => destruct H as [H | H]; break H
  | _ /\ _ =>
      let H' := fresh "B" in
      destruct H as [H H']; revert H'; break H;
      lazymatch goal with
      | |- ?P -> _ => let Hn := fresh "B" in intro Hn; lazymatch goal with Hm : P |- _ => break Hm end
      end
  | exists _, _ => let x := fresh "x" in destruct H as [x H]; break H
  | history_of _ _ = _ => scan H; inversion H; subst; clear H; learn
  | ?x = _ => first [is_var x; subst x | idtac]
  | _ = ?x => first [is_var x; subst x | idtac]
  | _ => idtac
  end.
Ltac reveal H := autounfold with frflow_defs in H; break H.

(** Nothing in the execution written out is what is said. *)
Ltac absent H := solve [reveal H].

(** One of the cases offered holds, by `tac`. *)
Ltac somewhere tac := first [solve [tac] | left; somewhere tac | right; somewhere tac].

(** A truth value of an execution is the proposition it stands for. *)
Lemma truth_is (P Q : Prop) : (P <-> Q) -> Value_Bool_ P = Value_Bool_ Q.
Proof. intros H. f_equal. apply propositional_extensionality. exact H. Qed.

(** The event at the moment `w`, in what is known and what is asked: one case for each event written out. *)
Ltac scan_at w :=
  let go evs :=
    let E := fresh "E" in let e := fresh "e" in let Ee := fresh "Ee" in
    pose proof (history_among evs w) as E; remember (history_of evs w) as e eqn:Ee in *; clear Ee;
    destruct E as [-> | E];
    [ | lazy in E;
        repeat (let Ew := fresh "Ew" in destruct E as [[Ew ->] | E]; [first [subst w | idtac] |]);
        try destruct E ] in
  lazymatch goal with
  | _ : context [history_of ?evs w] |- _ => go evs
  | |- context [history_of ?evs w] => go evs
  end.

(** No event written out is the call's own, where the moments asked of leave none. *)
Ltac no_direct Hits :=
  lazymatch type of Hits with
  | direct _ _ (history_of ?evs ?w) =>
      let E := fresh "E" in let e := fresh "e" in
      destruct (history_among evs w) as [E | E]; revert Hits E; generalize (history_of evs w); intros e Hits E;
      [ rewrite E in Hits; exact Hits
      | lazy in E;
        repeat (destruct E as [[-> ->] | E];
          [first [out_of_order | cbn in Hits; solve [intuition (first [congruence | lia])]] |]);
        exact (False_ind _ E) ]
  end.

(** The call made at a moment follows its program: none of its own events is before it nor after its response,
    and it goes on from its program to where it rests. *)
Ltac follows_go :=
  apply follows_of;
  [ let w := fresh "w" in let Hw := fresh "Hw" in let Hits := fresh "Hits" in
    intros w Hw Hits; no_direct Hits
  | let k := fresh "k" in let w := fresh "w" in let r := fresh "r" in let sp := fresh "sp" in
    let H := fresh "H" in let Hk := fresh "Hk" in let Hits := fresh "Hits" in
    intros k w r sp H Hk Hits; scan H; no_direct Hits
  | solve [go] ].

(** ** An execution written out is one of the code

    Each law of `Conforms`, of an execution written out: one case for each event the law speaks of. A call of a
    method or of a function of the code is found by its label and by what its first argument names, and
    followed from its program to where it rests. *)

(** Each call of a method of the code, on an object of the code, runs the method. *)
Ltac law_methods :=
  let H := fresh "H" in let Hy := fresh "Hy" in let Himpl := fresh "Himpl" in
  let Hm := fresh "Hm" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros ? ? ? ? ? ? ? ? ? H Hy Himpl; scan H; injection H as <- <- Hm <- <-;
  first
    [ solve [lazy in Hy; discriminate Hy]
    | solve [pose proof (plain_not_referred _ _ Hy) as Hr; discriminate Hr]
    | lazy in Hy; injection Hy as <- <-;
      pose proof (impl_labelled _ _ _ _ Himpl) as Hin; rewrite <- Hm in Hin; vm_compute in Hin;
      repeat (lazymatch type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end);
      first
        [ solve [destruct Hin]
        | subst; vm_compute in Himpl; first
            [ discriminate Himpl
            | injection Himpl as <-; eexists; split; [fact | split; [fact | follows_go]] ] ] ].

(** No call is of a method of an object alone of its class. *)
Ltac law_modules :=
  let H := fresh "H" in let Hc := fresh "Hc" in let Hmod := fresh "Hmod" in let Himpl := fresh "Himpl" in
  let Hm := fresh "Hm" in let Hin := fresh "Hin" in
  intros ? ? ? ? ? ? ? ? ? H Hc Hmod _ Himpl; pose proof (module_labelled _ _ _ _ _ _ Hc Hmod Himpl) as Hin;
  scan H; injection H as <- <- Hm <-; rewrite <- Hm in Hin; vm_compute in Hin; destruct Hin.

(** Each call that applies a function runs it. *)
Ltac law_functions :=
  let H := fresh "H" in let Happ := fresh "Happ" in let Hy := fresh "Hy" in let Hw := fresh "Hw" in
  let Hr := fresh "Hr" in
  intros ? ? ? ? ? ? ? H Happ Hy Hw; scan H; injection H as <- <- <- <- <-;
  first
    [ solve [vm_compute in Happ; discriminate Happ]
    | solve [lazy in Hy; discriminate Hy]
    | solve [pose proof (plain_not_referred _ _ Hy) as Hr; discriminate Hr]
    | lazy in Hy; injection Hy as <-; eexists; split; [fact | split; [fact | follows_go]] ].

(** No call made and responded to at once is one of the code. *)
Ltac law_atomic :=
  let H := fresh "H" in
  intros ? ? ? ? ? ? ? H; scan H; injection H as <- <- <- <- <- <-;
  (split;
   [ let Hm := fresh "Hm" in let Hys := fresh "Hys" in let Hy := fresh "Hy" in let Himpl := fresh "Himpl" in
     let Hr := fresh "Hr" in
     intros ? ? ? ? ? ? Hm Hys Hy Himpl;
     first [ discriminate Hys | injection Hys as <- <-; lazy in Hy; discriminate Hy
           | injection Hys as <- <-; pose proof (plain_not_referred _ _ Hy) as Hr; discriminate Hr ]
   | split;
     [ let Hm := fresh "Hm" in let Hc := fresh "Hc" in let Hmod := fresh "Hmod" in let Himpl := fresh "Himpl" in
       let Hin := fresh "Hin" in
       intros ? ? ? ? ? Hm Hc Hmod Himpl; pose proof (module_labelled _ _ _ _ _ _ Hc Hmod Himpl) as Hin;
       rewrite <- Hm in Hin; vm_compute in Hin; destruct Hin
     | let Happ := fresh "Happ" in let Hys := fresh "Hys" in let Hy := fresh "Hy" in let Hr := fresh "Hr" in
       intros ? ? ? Happ Hys Hy ?;
       first [ solve [vm_compute in Happ; discriminate Happ] | discriminate Hys
             | injection Hys as <- <-; lazy in Hy; discriminate Hy
             | injection Hys as <- <-; pose proof (plain_not_referred _ _ Hy) as Hr; discriminate Hr ] ] ]).

(** An object said to be made is one of the code, made once. *)
Ltac law_made :=
  let H := fresh "H" in let H' := fresh "H'" in
  split;
  [ intros ? ? ? ? ? ? H; scan H; injection H as <- <- <- <- <-; eexists; unfold names; reflexivity
  | intros ? ? ? ? ? ? ? ? ? ? ? H H'; scan H; injection H as <- <- <- <- <-; scan H';
    first [reflexivity | discriminate H'] ].

(** A call is responded to at most once, after it is made. *)
Ltac law_answered :=
  let H := fresh "H" in let H' := fresh "H'" in
  split;
  [ intros ? ? ? ? ? ? ? ? H H'; scan H; injection H as <- <- <- <-; scan H'; first [reflexivity | discriminate H']
  | intros ? ? ? ? ? H; scan H; injection H as <- <- <- <-; lia ].

(** A call of a constructor of a class of the code runs what making an object of the class runs. *)
Ltac law_constructors :=
  let H := fresh "H" in let Hc := fresh "Hc" in let Hmod := fresh "Hmod" in let Hm := fresh "Hm" in
  let Hin := fresh "Hin" in
  split;
  [ intros ? ? ? ? ? signature ? H Hc Hmod; pose proof (constructor_labelled _ _ signature _ Hc) as Hin;
    scan H; injection H as <- <- Hm <-; rewrite <- Hm in Hin; vm_compute in Hin;
    repeat (lazymatch type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end);
    first [ solve [destruct Hin]
          | subst; vm_compute in Hc; injection Hc as <-; eexists; split; [fact | split; [fact | follows_go]] ]
  | intros ? ? ? ? ? signature ? ? ? H Hc Hmod; pose proof (constructor_labelled _ _ signature _ Hc) as Hin;
    scan H; injection H as <- <- Hm <- <- <-; rewrite <- Hm in Hin; vm_compute in Hin; destruct Hin ].

(** Some moment from `n` on, within the fuel given, is one `tac` shows to be as asked. *)
Ltac seek n fuel tac :=
  lazymatch fuel with
  | O => fail "no such moment"
  | S ?f => first [exists n; tac | let n' := eval lazy in (n + 1) in seek n' f tac]
  end.

(** No event written out, at the moments asked of, is the write said. *)
Ltac no_write :=
  let Hw := fresh "Hw" in
  intros; intro Hw; scan Hw; first [discriminate Hw | lia].

(** What is read of a variable is what was last written there, or what it was made holding. *)
Ltac law_variables :=
  let H := fresh "H" in let Hyo := fresh "Hyo" in let Hvar := fresh "Hvar" in
  intros ? ? ? ? ? ? ? ? H Hyo Hvar ? ?; scan H; injection H as <- <- <- <- <-;
  first
    [ solve [lazy in Hyo; discriminate Hyo]
    | lazy in Hyo; injection Hyo as <- <-; first
        [ discriminate Hvar
        | right; split; [no_write | seek 0 400%nat ltac:(do 3 eexists; reflexivity)]
        | left; seek 0 400%nat ltac:(eexists; split; [lia | split; [reflexivity | no_write]]) ] ].

(** The execution written out is one of the code, under the naming given. *)
Ltac conforms_written :=
  split; [law_methods | split; [law_modules | split; [law_functions | split; [law_atomic | split; [law_made |
    split; [law_answered | split; [law_constructors | law_variables]]]]]]].

(** ** What a model says of an execution written out

    A model's words are its own (generated with it): these go by their shape, once unfolded. *)

(** The moment at which the call made at `i` by `a` is responded to, among the events written from `n` on. *)
Ltac respond_of evs a i n fuel k :=
  lazymatch fuel with
  | O => fail "the call is not responded to"
  | S ?f =>
      let e := eval lazy in (history_of evs n) in
      lazymatch e with
      | Event_Respond a i _ _ => k n
      | _ => let n' := eval lazy in (n + 1) in respond_of evs a i n' f k
      end
  end.

(** A call made has been responded to by some moment. *)
Ltac responded :=
  lazymatch goal with
  | |- exists to, _ (history_of ?evs) ?c ?from to =>
      let c' := eval lazy in c in let i' := eval lazy in from in let n := eval lazy in (i' + 1) in
      respond_of evs c' i' n 400%nat ltac:(fun r =>
        let r1 := eval lazy in (r + 1) in
        exists r1; autounfold with frflow_defs; exists r; do 2 eexists; split; [lia | reflexivity])
  end.

(** A call that is responded to makes its next event in time: its response, where it makes no other. *)
Ltac proceeds_written :=
  lazymatch goal with
  | |- _ (history_of ?evs) ?c ?i =>
      let c' := eval lazy in c in let i' := eval lazy in i in let n := eval lazy in (i' + 1) in
      respond_of evs c' i' n 400%nat ltac:(fun r =>
        let w := fresh "w" in let Hw := fresh "Hw" in let Hover := fresh "Hover" in
        let Hle := fresh "Hle" in let Hgt := fresh "Hgt" in
        autounfold with frflow_defs; intros w [[Hw Hover] _]; destruct (Z_le_gt_dec w r) as [Hle | Hgt];
        [ exists r; split; [exact Hle | right; do 2 eexists; reflexivity]
        | exfalso; apply Hover; exists r; do 2 eexists; split; [lia | reflexivity] ])
  end.

(** A truth value is not the one said. *)
Ltac untrue :=
  exfalso; learn;
  match goal with
  | H : (false = true) = True |- _ => assert (X : false = true) by (rewrite H; exact I); discriminate X
  | H : True = (false = true) |- _ => assert (X : false = true) by (rewrite <- H; exact I); discriminate X
  | H : (true = true) = False |- _ => rewrite <- H; reflexivity
  | H : False = (true = true) |- _ => rewrite H; reflexivity
  | H : (true = true) = (false = true) |- _ => exact (truths_differ (eq_sym H))
  | H : (false = true) = (true = true) |- _ => exact (truths_differ H)
  end.

(** Each moment `w` from `n` on, one after another (`tac`), then those past them (`last`). *)
Ltac each_moment w n fuel tac last :=
  lazymatch fuel with
  | O => last
  | S ?f =>
      let E := fresh "E" in
      destruct (Z.eq_dec w n) as [E | E];
      [ subst w; tac | let n' := eval lazy in (n + 1) in each_moment w n' f tac last ]
  end.

(** Some call the pending call itself made, before now, is not over. *)
Ltac between_from n fuel :=
  eexists; seek n fuel ltac:(split; [split; [lia | reflexivity] |];
    let H := fresh "H" in intros (? & ? & ? & ? & H); scan H; lia).

(** What a thread does at a moment written, while a call of its own is pending, is the call's own, or inside a
    call the call made that is not over: `Hlt` says the call was made before, `Hover` that it is not over,
    `Hdoes` what the thread does. *)
Ltac one_at Hdoes n fuel :=
  autounfold with frflow_defs in Hdoes; lazy in Hdoes;
  first
    [ solve [destruct Hdoes]
    | let Ht := fresh "Ht" in let Hi := fresh "Hi" in
      destruct Hdoes as [Ht Hi];
      first [ discriminate Ht | subst; first [left; reflexivity | right; between_from n fuel] ] ].
Ltac one_at_a_time Hlt Hover Hdoes :=
  lazymatch type of Hlt with
  | ?from < ?w =>
      lazymatch type of Hover with
      | ~ _ (history_of ?evs) ?t _ _ =>
          let t' := eval lazy in t in let n := eval lazy in (from + 1) in
          respond_of evs t' from n 400%nat ltac:(fun r =>
            let fuel := eval lazy in (Z.to_nat (r - from)) in
            each_moment w n fuel
              ltac:(one_at Hdoes n fuel)
              ltac:(exfalso; apply Hover; autounfold with frflow_defs; exists r; do 2 eexists;
                    split; [lia | reflexivity]))
      end
  end.
