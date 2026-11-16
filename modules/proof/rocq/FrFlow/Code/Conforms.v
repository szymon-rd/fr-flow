(** An execution of code read as trees.

    A model speaks of an execution: the event at each moment (`FrFlow.Executions`, generated from the model's
    vocabulary). Here is what it is for an execution to be one of some code, read from its TASTy as trees
    (`FrFlow.Scala.Tree`) whose meaning is `FrFlow.Scala.Meaning`.

    It is said call by call. A call of a method of the code, or of a function the code wrote, is made by one
    actor; the events that actor makes directly inside the call are the steps of the method's program, in
    order, one event for each operation: an object made, a field read or written, a call made and its response.
    Events of other actors, and events inside the calls the call makes, come between; nothing is said here of
    how they interleave. A call of what is outside the code (the JDK, a class not read) is an event with any
    response: what it gives is what the model assumes of it. Code with no meaning here (`Chaos`) may make any
    event.

    The execution's values are the code's by a naming: each value of the execution names at most one value of
    the code, and each value of the code has at most one name. Numbers, texts, truth values and unit are named
    by themselves. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Ascii.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Code.Outside.
Require FrFlow.Scala.Jdk.
Import ListNotations.
Open Scope string_scope.

Definition res : Type := Machine.res code obj.
Definition program : Type := Machine.P code obj res.

(** ** Names *)

(** Which value of the code a value of the execution is, and the class of the object at each place. What the
    JDK throws is known by its class alone, here as in the code's values. *)
Record naming := Naming {
  val_of : Value -> option val;
  class_at : nat -> string;
  of_unit : val_of Value_Unit_ = Some VUnit;
  of_bool : forall b : bool, val_of (Value_Bool_ (b = true)) = Some (VBool b);
  of_int : forall z, val_of (Value_Int_ z) = Some (vint z);
  of_str : forall s, val_of (Value_Str s) = Some (vstr s);
  of_thrown : forall cls, val_of (Value_Thrown cls) = Some (VExn (made_exn cls));
  of_null : val_of Value_Null = Some vnull;
  one_name : forall x y v, val_of x = Some v -> val_of y = Some v -> x = y;
  ref_class : forall x c r, val_of x = Some (vref c r) -> class_at r = c }.

Definition names (N : naming) (x : Value) (v : val) : Prop := val_of N x = Some v.

Lemma names_one (N : naming) x v w : names N x v -> names N x w -> v = w.
Proof. unfold names. intros H1 H2. rewrite H1 in H2. injection H2. auto. Qed.

(** What was thrown, as a value. *)
Definition thrown (x : exn) : val := match x with Thrown cls r => vref cls r | _ => VExn x end.

(** A response is the result. *)
Definition gives (N : naming) (a : Response) (x : res) : Prop :=
  match a, x with
  | Response_Returned y, inr v => names N y v
  | Response_Threw y, inl e => names N y (thrown e)
  | _, _ => False
  end.

(** ** Types

    What the JVM keeps of types, as far as a proof needs it: a truth value, a number and unit are those. What
    is known of a class the code mentions is read from its class file where the code is read (`classes`):
    whether its objects are known by their identity, whether it is a class of what is thrown, and which method
    a function is called by where it is taken as an interface. Of any other type nothing is said. *)

Record classes := Classes {
  identities : list string;    (* classes of the JDK that keep `Object`'s `equals`: an object is itself, no data *)
  throwables : list string;    (* classes of what is thrown *)
  functions : list string }.   (* the one method of each interface a function is taken as: its class and name *)

Definition reference (known : classes) (cls : string) : bool := existsb (String.eqb cls) (identities known).

Definition identity (v : val) : Prop :=
  match v with
  | VTid _ | VObj (Ext _ _) | VObj Null => True
  | VObj (Ref c _) => is_var c = false /\ c <> lazy_class   (* an object: not the place of a variable *)
  | _ => False
  end.

(** A type that says nothing of what its values are (`Any`, a value passed where any is taken), and the class
    of an object that is alone of its class. *)
Definition general (cls : string) : bool :=
  existsb (String.eqb cls) ["java.lang.Object"; "scala.Any"; "scala.AnyRef"; "scala.AnyVal"; "scala.Nothing";
    "scala.Null"; "scala.Matchable"; "scala.runtime.BoxedUnit"].

Fixpoint module_class (cls : string) : bool :=
  match cls with
  | EmptyString => false
  | String c EmptyString => Ascii.eqb c "$"%char
  | String _ rest => module_class rest
  end.

(** A class of what is thrown, and a value of one: none, or an exception. *)
Definition throwable (known : classes) (cls : string) : bool := existsb (String.eqb cls) (throwables known).

(** A value of any class is itself where a name holds it (the place of a variable and an argument passed by
    name are values of no class): that much is said even of a type that says nothing else. A set of Scala that
    does not change is the data it is made of. A value of any other class is also one a call can be made on:
    neither unit nor an object named alone. *)
Definition of_class (known : classes) (cls : string) (v : val) : Prop :=
  if String.eqb cls "scala.Unit" then v = VUnit
  else if String.eqb cls "scala.Boolean" then exists b, v = VBool b
  else if String.eqb cls "scala.Int" then exists z, v = vint z
  else if reference known cls then identity v
  else if general cls || module_class cls then held v = oret v
  else if throwable known cls then v = vnull \/ exists e, Jdk.as_exn v = Some e
  else if String.eqb cls c_set then exists xs, v = vdata c_set [VList xs]
  else held v = oret v /\ receiver v = [v].

Lemma identity_receiver (v : val) : identity v -> receiver v = [v].
Proof.
  destruct v as [| | | | o | |]; try contradiction; try reflexivity. destruct o; try contradiction; reflexivity.
Qed.

(** A reference is itself where a name holds it: no variable to read, no function to call. *)
Lemma held_identity (v : val) : identity v -> held v = oret v.
Proof.
  destruct v as [| | | | o | |]; try contradiction; try reflexivity. destruct o; try contradiction; try reflexivity.
  intros [H1 H2]. unfold held. rewrite H1, (proj2 (String.eqb_neq _ _) H2). reflexivity.
Qed.

(** What a signature says a definition gives: what follows its last colon. *)
Fixpoint after_last (s : string) : option string :=
  match s with
  | EmptyString => None
  | String c rest =>
      match after_last rest with
      | Some r => Some r
      | None => if Ascii.eqb c ":"%char then Some rest else None
      end
  end.

Definition returns (known : classes) (method : string) (x : res) : Prop :=
  match x, after_last method with
  | inr v, Some cls => of_class known cls v
  | _, _ => True
  end.

(** The method a function is called by where the code applies it itself (a local method called by its name, a
    function it holds applied): one name, whatever interface the function is of. What applies it from outside
    the code names the interface's method. *)
Definition function_apply : string := "scala.Function apply".

(** A call of a function is by the method of the interface it is taken as: of Scala's own function types, or
    of an interface with one method. Of these a call runs the function's body. *)
Definition applies (known : classes) (method : string) : bool :=
  existsb (fun p => String.prefix p method) (["scala.Function0 apply "; "scala.Function1 apply ";
    "scala.Function2 apply "; "scala.Function3 apply "; "scala.ContextFunction1 apply ";
    "scala.ContextFunction2 apply "; function_apply] ++ functions known).

Definition by_name_apply : string := "scala.Function0 apply :java.lang.Object".

Section Conforms.

  (** The code: its files, and the table of what they define (`Table.build`, computed where the files are). *)
  Variable files : list tree.
  Variable T : table.
  Variable known : classes.
  Definition run : code -> val -> program := Meaning.interp T Outside.outside Library.supers.

  Variable N : naming.

  (** A field as an execution names it: the class that declares it, and its name. *)
  Definition field_label (cls name : string) : string :=
    match named T cls name with
    | Some d => match def_sym d with Member owner n _ => owner ++ " " ++ n | _ => name end
    | None => name
    end.

  (** The class of what a field holds: of a variable, the class it was declared with. *)
  Definition field_class (cls name : string) : option string :=
    if is_var cls then var_holds cls else
    match named T cls name with
    | Some (ValDef _ _ t _) => ty_class t
    | _ => None
    end.

  Definition field_typed (cls name : string) (v : val) : Prop :=
    match field_class cls name with Some c => of_class known c v | None => True end.

  (** The object at a place, as the execution names it. *)
  Definition at_place (y : Value) (r : nat) : Prop := names N y (vref (class_at N r) r).

  Definition holding (cls : string) (fields : list (string * val)) (hs : list Executions.Held) : Prop :=
    Forall2 (fun fv h => Held_field h = field_label cls (fst fv) /\ names N (Held_value h) (snd fv)) fields hs.

  (** ** The event of an operation *)

  Definition op_event (a : Value) (i : Z) {X : Type} (o : Machine.op code obj X) : X -> Event -> Prop :=
    match o in Machine.op _ _ X return X -> Event -> Prop with
    | ObjNew cls fields => fun x e => exists r y hs,
        x = inr r /\ class_at N r = cls /\ names N y (vref cls r) /\ holding cls fields hs /\
        e = Event_Make a (Some i) y cls hs
    | ObjGet r f => fun x e => exists v y yo,
        x = inr v /\ at_place yo r /\ names N y v /\ field_typed (class_at N r) f v /\
        e = Event_Read a (Some i) yo (field_label (class_at N r) f) y
    | ObjMark r f => fun x e => exists yo,
        x = inr tt /\ at_place yo r /\ e = Event_Mark a (Some i) yo (field_label (class_at N r) f)
    | ObjSet r f v => fun x e => exists yo y,
        x = inr tt /\ at_place yo r /\ names N y v /\
        e = Event_Write a (Some i) yo (field_label (class_at N r) f) y
    | Enter r f what => fun x e => exists yo found,
        at_place yo r /\ e = Event_Enter a (Some i) yo (field_label (class_at N r) f) found /\
        match found, x with
        | None, inr None => True
        | Some y, inr (Some v) => names N y v
        | None, inl _ => True
        | _, _ => False
        end
    | _ => fun _ _ => False
    end.

  (** An operation with no event: what is not said here (a thread of the machine's own, an object of a class
      from outside by its protocol, code with no meaning). A call that reaches one may make any event. *)
  Definition unsaid {X : Type} (o : Machine.op code obj X) : Prop :=
    match o with
    | ObjNew _ _ | ObjGet _ _ | ObjMark _ _ | ObjSet _ _ _ | Enter _ _ _ | ExtCall _ _ _ => False
    | _ => True
    end.

  (** ** A call's steps *)

  (** What a program does next, past what makes no event: a loop's turn, an initialiser run where an object is
      made. *)
  Inductive settles : program -> program -> Prop :=
    | settled p : settles p p
    | settles_iter (S B : Type) (body : S -> Machine.P code obj (S + B)) s k p :
        settles (unfold_iter body s k) p -> settles (Iter body s k) p
    | settles_init cls arg k p :
        settles (pbind (run (Init cls) arg) k) p -> settles (Call (Init cls) arg k) p.

  (** Where a call is: running what is left of its program; waiting for the response of a call it made;
      ended; or lost, in code with no meaning. *)
  Inductive stage :=
    | Running (p : program)
    | Waiting (called : Z) (typed : res -> Prop) (k : res -> program)
    | Ended
    | Lost.

  Definition arguments (arg : val) : list val := match arg with VList vs => vs | _ => [] end.

  (** The method a function is called by where the code applies it: a by-name argument's is
      `Function0.apply`; any other's is `function_apply`. Both apply a function (`applies`), so what the call
      does is the function's body. *)
  Definition called_as (c : code) (arg : val) (method : string) : Prop :=
    match c, arg with
    | Thunk _ _, VUnit => method = by_name_apply
    | _, _ => method = function_apply
    end.

  (** One event of the call made at `i` by `a`, at the moment `w`: the call goes from one stage to the next. *)
  Inductive takes (a : Value) (i w : Z) (e : Event) : stage -> stage -> Prop :=
    | takes_op p X (o : Machine.op code obj X) k x :
        settles p (Vis o k) -> op_event a i o x e -> takes a i w e (Running p) (Running (k x))
    | takes_invoke p m args k ys :
        settles p (Vis (ExtCall 0 m args) k) -> Forall2 (names N) ys args ->
        e = Event_Invoke a (Some i) (Invocation_mk m ys) ->
        takes a i w e (Running p) (Waiting w (returns known m) k)
    | takes_atomic p m args k ys r spawns x :
        settles p (Vis (ExtCall 0 m args) k) -> Forall2 (names N) ys args ->
        e = Event_Atomic a (Some i) (Invocation_mk m ys) r spawns -> gives N r x -> returns known m x ->
        takes a i w e (Running p) (Running (k x))
    | takes_method p s on args k ys :
        settles p (Call (Method s) (VList (on :: args)) k) -> Forall2 (names N) ys (receiver on ++ args) ->
        e = Event_Invoke a (Some i) (Invocation_mk (label_of s) ys) ->
        takes a i w e (Running p) (Waiting w (fun _ => True) k)
    | takes_function p c arg k m y ys :
        settles p (Call c arg k) -> (match c with Fn _ _ _ | Thunk _ _ => True | _ => False end) ->
        called_as c arg m -> names N y (VCode c) -> Forall2 (names N) ys (arguments arg) ->
        e = Event_Invoke a (Some i) (Invocation_mk m (y :: ys)) ->
        takes a i w e (Running p) (Waiting w (fun _ => True) k)
    | takes_response called typed k r spawns x :
        e = Event_Respond a called r spawns -> gives N r x -> typed x ->
        takes a i w e (Waiting called typed k) (Running (k x))
    | takes_end p x r :
        settles p (Ret x) -> e = Event_Respond a i r [] -> gives N r x -> takes a i w e (Running p) Ended
    | takes_unsaid p X (o : Machine.op code obj X) k : settles p (Vis o k) -> unsaid o -> takes a i w e (Running p) Lost
    | takes_lost : takes a i w e Lost Lost.

  (** An event the call made at `i` by `a` makes itself: not one inside a call it makes. *)
  Definition direct (a : Value) (i : Z) (e : Event) : Prop :=
    match e with
    | Event_Invoke b inside _ | Event_Atomic b inside _ _ _ | Event_Make b inside _ _ _
    | Event_Read b inside _ _ _ | Event_Mark b inside _ _ | Event_Write b inside _ _ _
    | Event_Enter b inside _ _ _ => b = a /\ inside = Some i
    | Event_Respond b invoked _ _ => b = a /\ invoked = i
    | Event_Internal _ | Event_Stutter => False
    end.

  (** The response of the call it waits for. *)
  Definition answers (st : stage) (a : Value) (e : Event) : Prop :=
    match st, e with
    | Waiting called _ _, Event_Respond b invoked _ _ => b = a /\ invoked = called
    | _, _ => False
    end.

  Definition its (st : stage) (a : Value) (i : Z) (e : Event) : Prop := direct a i e \/ answers st a e.

  Variable history : Z -> Event.

  (** The call made at `i` by `a` runs `p`: it makes no event of its own before it is made, nor after it has
      responded; at each moment after it is made, the call is at a stage; an event of its own takes it to the
      next, and any other event leaves it where it is. *)
  Definition follows (a : Value) (i : Z) (p : program) : Prop :=
    (forall w, w <= i -> ~ direct a i (history w)) /\
    (forall k w r spawns, history k = Event_Respond a i r spawns -> k < w -> ~ direct a i (history w)) /\
    exists at_ : Z -> stage,
      at_ (i + 1) = Running p /\
      forall w, i < w ->
        (its (at_ w) a i (history w) -> takes a i w (history w) (at_ w) (at_ (w + 1))) /\
        (~ its (at_ w) a i (history w) -> at_ (w + 1) = at_ w).

  (** ** The calls of the code *)

  (** What a method's arguments are, by its parameters: one passed by name is a function. *)
  Definition passed (d : tree) (args : list val) : Prop :=
    Forall2 (fun p v =>
      if by_name p then exists b sc, v = VCode (Thunk b sc)
      else match p with
        | ValDef _ _ t _ => match ty_class t with Some c => of_class known c v | None => True end
        | _ => True
        end) (params d) args.

  (** A function the code wrote: its tree is among the code's. *)
  Definition written (c : code) : Prop :=
    match c with
    | Fn d _ _ => In d (over_list nodes files)
    | Thunk b _ => In b (over_list nodes files)
    | _ => False
    end.

  (** A call of a method of the code, on an object of the code whose class has it: its arguments are values of
      the code, of the method's parameters' types, and the call runs the method on them. *)
  Definition method_calls : Prop :=
    forall i a inside s cls r d y ys,
      history i = Event_Invoke a inside (Invocation_mk (label_of s) (y :: ys)) ->
      names N y (vref cls r) -> impl T cls s = Some d ->
      exists args, Forall2 (names N) ys args /\ passed d args /\
        follows a i (run (Method s) (VList (vref cls r :: args))).

  (** A call of a method of an object that is alone of its class. *)
  Definition module_calls : Prop :=
    forall i a inside owner name signature c d ys,
      history i = Event_Invoke a inside (Invocation_mk (label owner name signature) ys) ->
      class_of T owner = Some c -> is_module c = true -> impl T owner (Member owner name signature) = Some d ->
      exists args, Forall2 (names N) ys args /\ passed d args /\
        follows a i (run (Method (Member owner name signature)) (VList (module_val T owner :: args))).

  (** What a function is given, by its parameters: as a method's arguments are. *)
  Definition given (c : code) (args : list val) : Prop :=
    match c with Fn d _ _ => passed d args | _ => True end.

  (** A call of a function the code wrote. *)
  Definition function_calls : Prop :=
    forall i a inside m c y ys,
      history i = Event_Invoke a inside (Invocation_mk m (y :: ys)) ->
      applies known m = true -> names N y (VCode c) -> written c ->
      exists args, Forall2 (names N) ys args /\ given c args /\ follows a i (run c (VList args)).

  (** A call of the code is no event made and responded to at once. *)
  Definition never_atomic : Prop :=
    forall w a inside m ys resp spawns,
      history w = Event_Atomic a inside (Invocation_mk m ys) resp spawns ->
      (forall s cls r d y ys', m = label_of s -> ys = y :: ys' -> names N y (vref cls r) ->
         impl T cls s = Some d -> False) /\
      (forall owner name signature c d, m = label owner name signature -> class_of T owner = Some c ->
         is_module c = true -> impl T owner (Member owner name signature) = Some d -> False) /\
      (forall c y ys', applies known m = true -> ys = y :: ys' -> names N y (VCode c) -> written c -> False).

  (** An object the execution says is made is an object of the code, made once. *)
  Definition made_once : Prop :=
    (forall w b inside y cls hs, history w = Event_Make b inside y cls hs -> exists r, names N y (vref cls r)) /\
    (forall w w' b inside y cls hs b' inside' cls' hs',
        history w = Event_Make b inside y cls hs -> history w' = Event_Make b' inside' y cls' hs' -> w = w').

  (** A call is responded to at most once, after it is made. *)
  Definition answered_once : Prop :=
    (forall k k' a called r r' spawns spawns',
      history k = Event_Respond a called r spawns -> history k' = Event_Respond a called r' spawns' -> k = k') /\
    (forall k a called r spawns, history k = Event_Respond a called r spawns -> called < k).

  (** The execution is one of the code. *)
  Definition conforms : Prop :=
    method_calls /\ module_calls /\ function_calls /\ never_atomic /\ made_once /\ answered_once.

End Conforms.

(** The execution is one of the code read: under some naming of its values. *)
Definition runs (files : list tree) (T : table) (known : classes) (history : Z -> Event) : Prop :=
  exists N : naming, conforms files T known N history.
