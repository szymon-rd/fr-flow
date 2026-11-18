(** What the machine checks of a step before it takes it.

    An execution of the code (`Conforms`) says more of a call than the machine's step does: that the arguments
    of a method of the code are of its parameters' types, that what a call gives is of the type its signature
    says, and, from the label of a call and what it is made on alone, which program the call runs. The machine
    (`Frames`) has the values, so it can check each: here is each check as a computation, and that it gives what
    `Conforms` asks (`…_sound`, `agreed_…`). A step that fails a check is refused: the run stops there, and says
    why.

    - A value is of a class (`of_class_b`), arguments are a method's (`passed_b`), a result is a signature's
      (`returns_b`), a field's value is of the field's class (`field_typed_b`).
    - `agreed`: a call made by its label `m`, showing the values `vs`, runs what every law of `Conforms` that
      speaks of such a call says it runs; and no law speaks of it where the machine runs what the library says. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Ascii.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Equal FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require FrFlow.Scala.Jdk.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms.
Import ListNotations.
Local Open Scope string_scope.

(** ** A label read back *)

(** Each way to cut a text at one of its spaces. *)
Fixpoint splits (s : string) : list (string * string) :=
  match s with
  | EmptyString => []
  | String c rest =>
      ((if Ascii.eqb c " "%char then [(EmptyString, rest)] else []) ++
       map (fun ab => (String c (fst ab), snd ab)) (splits rest))%list
  end.

Lemma splits_in (a b : string) : In (a, b) (splits (a ++ " " ++ b)).
Proof.
  induction a as [| c a IH]; cbn.
  - left. reflexivity.
  - apply in_or_app. right. apply in_map_iff. exists (a, b). split; [reflexivity | exact IH].
Qed.

(** Each definition a label can be of: an owner, a name and a signature. *)
Definition parses (m : string) : list (string * string * string) :=
  flat_map (fun ab => map (fun ng => (fst ab, fst ng, snd ng)) (splits (snd ab))) (splits m).

Lemma parses_in (o n g : string) : In (o, n, g) (parses (label o n g)).
Proof.
  unfold parses, label. apply in_flat_map. exists (o, n ++ " " ++ g). split; [apply splits_in |].
  cbn [fst snd]. apply in_map_iff. exists (n, g). split; [reflexivity | apply splits_in].
Qed.

Lemma label_parses (s : sym) (m : string) :
  label_of s = m -> m <> "" -> exists o n g, s = Member o n g /\ In (o, n, g) (parses m).
Proof.
  destruct s as [| o n g |]; cbn; intros <- H; try (destruct H; reflexivity).
  exists o, n, g. split; [reflexivity | apply parses_in].
Qed.

(** ** Values of a class *)

(** A value that is itself where a name holds it. *)
Definition held_plain (v : val) : bool :=
  match v with
  | VObj (Ref c _) => negb (is_var c) && negb (String.eqb c lazy_class)
  | VCode (Thunk _ _) => false
  | VCode (Fn (DefDef _ _ [] _ _ _) _ _) => false
  | _ => true
  end.

Lemma held_plain_sound (v : val) : held_plain v = true -> held v = oret v.
Proof.
  destruct v as [| | | | o | c |]; try reflexivity.
  - destruct o; try reflexivity. cbn.
    destruct (is_var cls); [discriminate |]. destruct (String.eqb cls lazy_class); [discriminate | reflexivity].
  - destruct c as [d sc group | | | |]; try reflexivity; try discriminate.
    destruct d; try reflexivity. destruct paramss; [discriminate | reflexivity].
Qed.

Definition identity_b (v : val) : bool :=
  match v with
  | VTid _ | VObj (Ext _ _) | VObj Null => true
  | VObj (Ref c _) => negb (is_var c) && negb (String.eqb c lazy_class)
  | _ => false
  end.

Lemma identity_b_sound (v : val) : identity_b v = true -> identity v.
Proof.
  destruct v as [| | | | o | |]; try discriminate; try (intros _; exact I).
  destruct o; try discriminate; try (intros _; exact I). cbn. intros H.
  apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H1, H2.
  split; [exact H1 | apply String.eqb_neq; exact H2].
Qed.

Fixpoint all2 {A B : Type} (f : A -> B -> bool) (xs : list A) (ys : list B) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => f x y && all2 f xs' ys'
  | _, _ => false
  end.

Lemma all2_Forall2 {A B : Type} (f : A -> B -> bool) (P : A -> B -> Prop) :
  (forall x y, f x y = true -> P x y) -> forall xs ys, all2 f xs ys = true -> Forall2 P xs ys.
Proof.
  intros Hf. induction xs as [| x xs IH]; intros [| y ys] H; cbn in H; try discriminate; constructor.
  - apply Hf. apply andb_true_iff in H. apply H.
  - apply IH. apply andb_true_iff in H. apply H.
Qed.

Section Checks.

  Variable T : table.
  Variable known : classes.

  Definition among (cls : string) (names : list string) : bool := existsb (String.eqb cls) names.

  Lemma among_in (cls : string) (names : list string) : among cls names = true -> In cls names.
  Proof.
    intros H. apply existsb_exists in H as (x & Hx & E). apply String.eqb_eq in E. subst x. exact Hx.
  Qed.

  Definition of_class_b (cls : string) (v : val) : bool :=
    if String.eqb cls "scala.Unit" then match v with VUnit => true | _ => false end
    else if String.eqb cls "scala.Boolean" then match v with VBool _ => true | _ => false end
    else if String.eqb cls "scala.Int" then match v with VObj (Int _) => true | _ => false end
    else if reference known cls then
      identity_b v && match v with VObj (Ref c _) => among c (heirs known) | _ => true end
    else if general cls || module_class cls then held_plain v
    else if throwable known cls then
      match v with VObj Null | VExn _ | VObj (Ref _ _) => true | _ => false end
    else if String.eqb cls c_set then
      match v with VObj (Data c [VList _]) => String.eqb c c_set | _ => false end
    else if function_class cls then
      match v with
      | VCode (Fn _ _ _) => held_plain v
      | VObj (Ref c _) => among c (heirs known)
      | _ => false
      end
    else if String.eqb cls "scala.Option" then
      match v with
      | VObj Null => true
      | VObj (Data c []) => String.eqb c c_none
      | VObj (Data c [x]) => String.eqb c c_some && held_plain x
      | _ => false
      end
    else if among cls (objects known) then held_plain v && match v with VUnit => false | _ => true end
    else held_plain v && match v with VUnit | VObj (Module _) => false | _ => true end.

  Lemma of_class_b_sound (cls : string) (v : val) : of_class_b cls v = true -> of_class known cls v.
  Proof.
    unfold of_class_b, of_class.
    destruct (String.eqb cls "scala.Unit"); [destruct v; try discriminate; reflexivity |].
    destruct (String.eqb cls "scala.Boolean"); [destruct v; try discriminate; eauto |].
    destruct (String.eqb cls "scala.Int").
    { destruct v as [| | | | o | |]; try discriminate. destruct o; try discriminate. intros _. eexists. reflexivity. }
    destruct (reference known cls).
    { intros H. apply andb_true_iff in H as [H1 H2]. split; [apply identity_b_sound, H1 |].
      intros c r ->. apply among_in. exact H2. }
    destruct (general cls || module_class cls); [apply held_plain_sound |].
    destruct (throwable known cls).
    { destruct v as [| | | e | o | |]; try discriminate; [intros _; right; exists e; reflexivity |].
      destruct o; try discriminate; intros _; first [left; reflexivity | right; eexists; reflexivity]. }
    destruct (String.eqb cls c_set).
    { destruct v as [| | | | o | |]; try discriminate. destruct o as [| | | | | | | c args | |]; try discriminate.
      destruct args as [| x rest]; try discriminate. destruct x; try discriminate.
      destruct rest; try discriminate. intros H. apply String.eqb_eq in H. subst c. eexists. reflexivity. }
    destruct (function_class cls).
    { destruct v as [| | | | o | c |]; try discriminate.
      - destruct o; try discriminate. intros H. right. do 2 eexists. split; [reflexivity | apply among_in, H].
      - destruct c as [d sc group | | | |]; try discriminate. intros H. left. exists d, sc, group.
        split; [reflexivity | apply held_plain_sound, H]. }
    destruct (String.eqb cls "scala.Option").
    { destruct v as [| | | | o | |]; try discriminate. destruct o as [| | | | | | | c args | |]; try discriminate.
      - intros _. right. right. reflexivity.
      - destruct args as [| x rest].
        + intros H. apply String.eqb_eq in H. subst c. left. reflexivity.
        + destruct rest; try discriminate. intros H. apply andb_true_iff in H as [H1 H2].
          apply String.eqb_eq in H1. subst c. right. left. exists x.
          split; [reflexivity | apply held_plain_sound, H2]. }
    unfold among. destruct (existsb (String.eqb cls) (objects known)).
    - intros H. apply andb_true_iff in H as [H1 H2]. split; [apply held_plain_sound, H1 |].
      destruct v as [| | | | o | |]; try discriminate; try (left; reflexivity).
      destruct o; try (left; reflexivity). right. eexists. reflexivity.
    - intros H. apply andb_true_iff in H as [H1 H2]. split; [apply held_plain_sound, H1 |].
      destruct v as [| | | | o | |]; try discriminate; try reflexivity. destruct o; try discriminate; reflexivity.
  Qed.

  (** An argument is its parameter's: a function where it is passed by name, else of the parameter's class. *)
  Definition param_ok (p : tree) (v : val) : bool :=
    if by_name p then match v with VCode (Thunk _ _) => true | _ => false end
    else match p with
      | ValDef _ _ t _ => match ty_class t with Some c => of_class_b c v | None => true end
      | _ => true
      end.

  Definition passed_b (d : tree) (args : list val) : bool := all2 param_ok (params d) args.

  Lemma passed_b_sound (d : tree) (args : list val) : passed_b d args = true -> passed known d args.
  Proof.
    apply all2_Forall2. intros p v. unfold param_ok. destruct (by_name p).
    - destruct v as [| | | | | c |]; try discriminate. destruct c; try discriminate. eauto.
    - destruct p; try (intros _; exact I). destruct (ty_class _); [apply of_class_b_sound | intros _; exact I].
  Qed.

  Definition given_b (c : code) (args : list val) : bool :=
    match c with Fn d _ _ => passed_b d args | _ => true end.

  Lemma given_b_sound (c : code) (args : list val) : given_b c args = true -> given known c args.
  Proof. destruct c; try (intros _; exact I). apply passed_b_sound. Qed.

  Definition returns_b (m : string) (x : res) : bool :=
    match x with
    | inr v => match after_last m with Some cls => of_class_b cls v | None => true end
    | inl (Thrown cls r) => identity_b (vref cls r)
    | inl _ => true
    end.

  Lemma returns_b_sound (m : string) (x : res) : returns_b m x = true -> returns known m x.
  Proof.
    destruct x as [e | v]; cbn.
    - destruct e; try (intros _; exact I). exact (identity_b_sound (vref class r)).
    - destruct (after_last m); [apply of_class_b_sound | intros _; exact I].
  Qed.

  Definition field_typed_b (cls name : string) (v : val) : bool :=
    match field_class T cls name with Some c => of_class_b c v | None => true end.

  Lemma field_typed_b_sound (cls name : string) (v : val) :
    field_typed_b cls name v = true -> field_typed T known cls name v.
  Proof.
    unfold field_typed_b, field_typed. destruct (field_class T cls name); [apply of_class_b_sound | intros _; exact I].
  Qed.

  (** ** What a call runs *)

  (** What a call made by a label runs: a method of the code on what it is called on, or a function. *)
  Inductive intent :=
    | AsMethod (s : sym) (on : val) (args : list val)
    | AsFunction (c : code) (args : list val).

  Definition does (x : intent) : program :=
    match x with
    | AsMethod s on args => run T (Method s) (VList (on :: args))
    | AsFunction c args => run T c (VList args)
    end.

  Definition intent_eqb (x y : intent) : bool :=
    match x, y with
    | AsMethod s on args, AsMethod s' on' args' =>
        (if sym_eq_dec s s' then true else false) && val_eqb (VList (on :: args)) (VList (on' :: args'))
    | AsFunction c args, AsFunction c' args' => val_eqb (VList (VCode c :: args)) (VList (VCode c' :: args'))
    | _, _ => false
    end.

  Lemma intent_eqb_eq (x y : intent) : intent_eqb x y = true -> x = y.
  Proof.
    destruct x as [s on args | c args], y as [s' on' args' | c' args']; cbn; try discriminate.
    - destruct (sym_eq_dec s s') as [-> |]; [| discriminate]. cbn. intros H. apply val_eqb_eq in H.
      injection H as -> ->. reflexivity.
    - intros H. apply val_eqb_eq in H. injection H as -> ->. reflexivity.
  Qed.

  (** What `method_calls` and `module_calls` say a call of the label `m` showing `vs` runs: for each definition
      the label can be of, the method on the object shown first, where its class has it; and the method on the
      object alone of its class, where that object has no state. Each with the method's definition. *)
  Definition meant_methods (m : string) (vs : list val) : list (intent * tree) :=
    flat_map (fun ong =>
      let s := Member (fst (fst ong)) (snd (fst ong)) (snd ong) in
      let o := fst (fst ong) in
      ((match vs with
       | VObj (Ref cls r) :: rest =>
           match impl T cls s with Some d => [(AsMethod s (vref cls r) rest, d)] | None => [] end
       | _ => []
       end) ++
      (match class_of T o with
       | Some c =>
           if is_module c then
             match module_at T o, impl T o s with
             | None, Some d => [(AsMethod s (module_val T o) vs, d)]
             | _, _ => []
             end
           else []
       | None => []
       end))%list) (parses m).

  (** What `function_calls` says it runs. *)
  Definition meant_function (m : string) (vs : list val) : list intent :=
    if applies known m then match vs with VCode c :: rest => [AsFunction c rest] | _ => [] end else [].

  (** Whether `constructor_calls` speaks of it: the constructor of a class of the code. *)
  Definition meant_made (m : string) : bool :=
    existsb (fun ong =>
      String.eqb (snd (fst ong)) "<init>" &&
      match class_of T (fst (fst ong)) with Some c => negb (is_module c) | None => false end) (parses m).

  (** The call runs `act` (the library's program, where there is none), and that is what every law says. *)
  Definition agreed (m : string) (vs : list val) (act : option intent) : bool :=
    negb (String.eqb m "") && negb (meant_made m) &&
    forallb (fun xd =>
      match act with
      | Some y =>
          intent_eqb (fst xd) y &&
          match fst xd with AsMethod _ _ args => passed_b (snd xd) args | AsFunction _ _ => true end
      | None => false
      end) (meant_methods m vs) &&
    forallb (fun x =>
      match act with
      | Some y => intent_eqb x y && match x with AsFunction c args => given_b c args | AsMethod _ _ _ => true end
      | None => false
      end) (meant_function m vs).

  (** A value, as a run that stops says it: the class the meaning takes it for, or what kind of value it is. *)
  Definition said_of (v : val) : string :=
    match v with
    | VObj (Module m) => cat "the object " m
    | VObj Null => "no object"
    | VCode (Fn _ _ _) => "a function"
    | VCode (Thunk _ _) => "an argument by name"
    | VCode _ => "a method"
    | _ => match class_of_val v with Some c => cat "a " c | None => "a value" end
    end.

  (** The first argument that is not its parameter's. *)
  Fixpoint ill_typed (ps : list tree) (vs : list val) : string :=
    match ps, vs with
    | p :: ps', v :: vs' =>
        if param_ok p v then ill_typed ps' vs'
        else cat (said_of v) (cat " for " (match p with
          | ValDef _ _ t _ => match ty_class t with Some c => c | None => "a parameter" end
          | _ => "a parameter" end))
    | [], [] => ""
    | _, _ => "more or fewer arguments than parameters"
    end.

  (** Why a call is not agreed, for the run to say. *)
  Definition disagreement (m : string) (vs : list val) (act : option intent) : string :=
    let same (x : intent) := match act with Some y => intent_eqb x y | None => false end in
    if String.eqb m "" then "a call with no label"
    else if meant_made m then cat "the constructor of a class of the code, called by its label: " m
    else match find (fun xd => negb (same (fst xd))) (meant_methods m vs) with
      | Some _ => cat "a call that is of a method of the code and runs something else: " m
      | None =>
          match find (fun x => negb (same x)) (meant_function m vs) with
          | Some _ => cat "a call that applies a function and runs something else: " m
          | None =>
              let wrong := (flat_map (fun xd => match fst xd with
                | AsMethod _ _ args => if passed_b (snd xd) args then [] else [ill_typed (params (snd xd)) args]
                | AsFunction _ _ => [] end) (meant_methods m vs) ++
                flat_map (fun x => match x with
                | AsFunction (Fn d _ _) args => if passed_b d args then [] else [ill_typed (params d) args]
                | _ => [] end) (meant_function m vs))%list in
              cat "an argument that is not of its parameter's type, " (cat (hd "" wrong) (cat ", in a call of " m))
          end
      end.

  Lemma agreed_parts (m : string) (vs : list val) (act : option intent) :
    agreed m vs act = true ->
    m <> "" /\ meant_made m = false /\
    (forall x d, In (x, d) (meant_methods m vs) ->
       act = Some x /\ match x with AsMethod _ _ args => passed known d args | AsFunction _ _ => True end) /\
    (forall x, In x (meant_function m vs) ->
       act = Some x /\ match x with AsFunction c args => given known c args | AsMethod _ _ _ => True end).
  Proof.
    unfold agreed. intros H. apply andb_true_iff in H as [H Hf]. apply andb_true_iff in H as [H Hm].
    apply andb_true_iff in H as [H0 H1]. apply negb_true_iff in H0, H1. apply String.eqb_neq in H0.
    rewrite forallb_forall in Hm, Hf. repeat split; try assumption.
    - specialize (Hm _ H). cbn [fst snd] in Hm. destruct act as [y |]; [| discriminate].
      apply andb_true_iff in Hm as [E _]. apply intent_eqb_eq in E. subst y. reflexivity.
    - specialize (Hm _ H). cbn [fst snd] in Hm. destruct act as [y |]; [| discriminate].
      apply andb_true_iff in Hm as [_ P]. destruct x; [apply passed_b_sound, P | exact I].
    - specialize (Hf _ H). destruct act as [y |]; [| discriminate].
      apply andb_true_iff in Hf as [E _]. apply intent_eqb_eq in E. subst y. reflexivity.
    - specialize (Hf _ H). destruct act as [y |]; [| discriminate].
      apply andb_true_iff in Hf as [_ P]. destruct x; [exact I | apply given_b_sound, P].
  Qed.

  (** A call the machine made of a method of the code, on an object whose class has it, ran that method on it,
      with arguments of its parameters' types. *)
  Lemma agreed_method (m : string) (vs : list val) (act : option intent) s cls r d rest :
    agreed m vs act = true -> label_of s = m -> vs = vref cls r :: rest -> impl T cls s = Some d ->
    act = Some (AsMethod s (vref cls r) rest) /\ passed known d rest.
  Proof.
    intros H Hs -> Hd. destruct (agreed_parts _ _ _ H) as (Hm & _ & Hmeth & _).
    destruct (label_parses s m Hs Hm) as (o & n & g & -> & Hin).
    apply (Hmeth (AsMethod (Member o n g) (vref cls r) rest) d).
    unfold meant_methods. apply in_flat_map. exists (o, n, g). split; [exact Hin |].
    cbn [fst snd vref]. rewrite Hd. left. reflexivity.
  Qed.

  (** One of a method of an object alone of its class, with no state, ran that method on the object. *)
  Lemma agreed_module (m : string) (vs : list val) (act : option intent) owner name signature c d :
    agreed m vs act = true -> m = label owner name signature -> class_of T owner = Some c ->
    is_module c = true -> module_at T owner = None -> impl T owner (Member owner name signature) = Some d ->
    act = Some (AsMethod (Member owner name signature) (module_val T owner) vs) /\ passed known d vs.
  Proof.
    intros H -> Hc Hmod Hat Hd. destruct (agreed_parts _ _ _ H) as (_ & _ & Hmeth & _).
    apply (Hmeth (AsMethod (Member owner name signature) (module_val T owner) vs) d).
    unfold meant_methods. apply in_flat_map. exists (owner, name, signature). split; [apply parses_in |].
    cbn [fst snd]. apply in_or_app. right. rewrite Hc, Hmod, Hat, Hd. left. reflexivity.
  Qed.

  (** One that applies a function ran the function. *)
  Lemma agreed_function (m : string) (vs : list val) (act : option intent) c rest :
    agreed m vs act = true -> applies known m = true -> vs = VCode c :: rest ->
    act = Some (AsFunction c rest) /\ given known c rest.
  Proof.
    intros H Happ ->. destruct (agreed_parts _ _ _ H) as (_ & _ & _ & Hfun).
    apply (Hfun (AsFunction c rest)). unfold meant_function. rewrite Happ. left. reflexivity.
  Qed.

  (** None is of the constructor of a class of the code. *)
  Lemma agreed_made (m : string) (vs : list val) (act : option intent) cls signature c :
    agreed m vs act = true -> m = label cls "<init>" signature -> class_of T cls = Some c ->
    is_module c = false -> False.
  Proof.
    intros H -> Hc Hmod. destruct (agreed_parts _ _ _ H) as (_ & Hmade & _).
    assert (meant_made (label cls "<init>" signature) = true) as X; [| rewrite X in Hmade; discriminate Hmade].
    unfold meant_made. apply existsb_exists. exists (cls, "<init>", signature). split; [apply parses_in |].
    cbn [fst snd]. rewrite Hc, Hmod. reflexivity.
  Qed.

End Checks.
