(** What staged code is written with.

    Code read as trees is given its meaning by `Meaning.denote`, which a proof computes step by step. Staged code
    is that meaning computed where the code is read (`frflow.core.staged.Stage`): one program per method, per
    initialiser, per function made in the code and per argument taken unevaluated, written with the functions
    here. Each does what `Meaning` does where the tree has that form, on values: what `Meaning` reads of the
    tree and of the scope is already read.

    `bodies` is what `Conforms.run` asks first: the program of what is called, where it was staged. *)

From Stdlib Require Import String List ZArith Bool.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Scala.Library FrFlow.Code.Outside.
Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.
Open Scope meaning_scope.

(** A value given: `oret`, of a value. *)
Abbreviation give v := (@oret val v) (only parsing).

Definition context (T : table) : Meaning.context :=
  Context (equal T) (fun x cls => instance T Library.supers x (TyRef cls)).

(** ** Calls outside the code *)

(** A definition from outside called on evaluated arguments (`Meaning.call_outside`). One that takes an
    argument unevaluated is not called so: it is stuck. *)
Definition out (T : table) (s : sym) (on : val) (targs : list ty) (args : list val) : D :=
  match s with
  | Member owner name signature =>
      match Outside.outside owner name signature with
      | Some p =>
          if existsb (fun b => b) (firstn (List.length args) (p_lazy p))
          then stuck "an argument taken unevaluated, given evaluated"
          else p_run p (context T) on targs args
      | None =>
          match args with
          | [] =>
              if String.eqb signature "" || String.eqb signature "package"
              then oret (VObj (Module (owner ++ "." ++ name)))
              else stuck ("a definition from outside with no meaning here: " ++ owner ++ "." ++ name)
          | _ => stuck ("a definition from outside with no meaning here: " ++ owner ++ "." ++ name)
          end
      end
  | _ => stuck "a definition from outside that is no member"
  end.

(** The arguments of a call that takes some unevaluated (`Meaning.eval_args`): each is given as the value kept
    for later, or as the program that evaluates it now, as the definition takes it. *)
Fixpoint lazily (lazy : list bool) (args : list (val + D)) : X (list val) :=
  match args with
  | [] => oret []
  | a :: rest =>
      match lazy, a with
      | true :: lazy', inl kept => vs <~ lazily lazy' rest ;; oret (kept :: vs)
      | false :: lazy', inr d => v <~ d ;; vs <~ lazily lazy' rest ;; oret (v :: vs)
      | [], inr d => v <~ d ;; vs <~ lazily [] rest ;; oret (v :: vs)
      | _, _ => stuck "an argument given otherwise than the definition takes it"
      end
  end.

Definition out_lazy (T : table) (s : sym) (on : val) (targs : list ty) (args : list (val + D)) : D :=
  match s with
  | Member owner name signature =>
      match Outside.outside owner name signature with
      | Some p => vs <~ lazily (p_lazy p) args ;; p_run p (context T) on targs vs
      | None => stuck ("a definition from outside with no meaning here: " ++ owner ++ "." ++ name)
      end
  | _ => stuck "a definition from outside that is no member"
  end.

(** The staging takes a definition from outside to take the arguments `lazy` unevaluated, where it decides how
    each argument is given (`out`, `out_lazy`): it is so where the library says the same. *)
Definition takes (s : sym) (lazy : list bool) : bool :=
  match s with
  | Member owner name signature =>
      match Outside.outside owner name signature with
      | Some p => if list_eq_dec Bool.bool_dec (p_lazy p) lazy then true else false
      | None => match lazy with [] => true | _ => false end
      end
  | _ => false
  end.

(** A method declared outside, called on a value: the object's own, where it is an object of the code that has
    it (`Meaning.select_with`). *)
Definition own (T : table) (s : sym) (on : val) (targs : list ty) (args : list val) : D :=
  match implemented T on s with
  | Some d =>
      if existsb by_name (params d) then stuck "an argument taken unevaluated, given evaluated"
      else call_method s on args
  | None => out T s on targs args
  end.

(** ** What is said of every value (`Meaning.universal`) *)

Definition truth (m : X bool) : D := b <~ m ;; oret (VBool b).
Definition eq_ (T : table) (a b : val) : D := truth (equal T a b).
Definition ne_ (T : table) (a b : val) : D := truth (r <~ equal T a b ;; oret (negb r)).
Definition same_ (T : table) (a b : val) : D :=
  match same_val T 1 a b with
  | Some r => oret (VBool r)
  | None => stuck "two objects compared for identity that this meaning cannot tell apart"
  end.
Definition is_instance (T : table) (v : val) (t : ty) : D :=
  match instance T Library.supers v t with
  | Some b => oret (VBool b)
  | None => stuck "a test of a type that is not a class"
  end.
Definition as_instance (T : table) (v : val) (t : ty) : D :=
  match instance T Library.supers v t with
  | Some false => match v with VObj Null => oret v | _ => othrow (Machine.Other "java.lang.ClassCastException") end
  | _ => oret v
  end.

(** ** Variables, fields, objects *)

Definition held (T : table) (v : val) : D := Meaning.held v.
Definition get_field (T : table) (v : val) (name : string) : D := Meaning.get_field v name.
Definition set_field (T : table) (v : val) (name : string) (x : val) : D := Meaning.set_field T v name x.
Definition call_method (T : table) (s : sym) (on : val) (args : list val) : D := Meaning.call_method s on args.
Definition module_obj (T : table) (cls : string) : D := Meaning.module_obj T cls.
Definition captured (T : table) (on : val) : X scope := Meaning.captured on.

Definition new_var (T : table) (cls : string) (v : val) : D :=
  r <~ oop (ObjNew cls [(var_field, v)]) ;; oret (vref cls r).

Definition set_var (T : table) (x v : val) : D :=
  match x with
  | VObj (Ref _ r) => _ <~ oop (ObjMark r var_field) ;; _ <~ oop (ObjSet r var_field v) ;; oret VUnit
  | _ => stuck "an assignment to what is no variable"
  end.

(** A function made in the code, called (`Meaning.call_local`). *)
Definition apply_ (T : table) (f : val) (args : list val) : D :=
  match f with
  | VCode c => ocall c (VList args)
  | _ => stuck "a call of what is no function"
  end.

(** An object of a class of the code made (`Meaning.construct`): one of a class written inside a method keeps
    the variables in scope where it is made. *)
Definition construct_ (T : table) (cls : string) (kept : scope) (vs : list val) : D :=
  r <~ oop (ObjNew cls (fields_of T cls ++ if is_local cls then [(scope_field, scope_val kept)] else [])) ;;
  _ <~ ocall (Init cls) (VList (vref cls r :: vs)) ;;
  oret (vref cls r).

Definition init_ (T : table) (cls : string) (this : val) (vs : list val) : D := ocall (Init cls) (VList (this :: vs)).

(** ** What a unit was given to keep *)

Definition found (sc : scope) (k : string) : val := match lookup sc k with Some v => v | None => VUnit end.

Definition sought (T : table) (sc : scope) (k : string) : D :=
  match lookup sc k with
  | Some v => Meaning.held v
  | None => stuck ("a variable that is not in scope: " ++ k)
  end.

Definition assign_sought (T : table) (sc : scope) (k : string) (v : val) : D :=
  match lookup sc k with
  | Some x => set_var T x v
  | None => stuck ("an assignment to what is no variable: " ++ k)
  end.

Definition call_sought (T : table) (sc : scope) (k : string) (vs : list val) : D :=
  match lookup sc k with
  | Some (VCode (Fn d sc' group)) =>
      if existsb by_name (params d) then stuck "an argument taken unevaluated, given evaluated"
      else ocall (Fn d sc' group) (VList vs)
  | Some _ => stuck ("a call of what is no function: " ++ k)
  | None => stuck ("a function that is not in scope: " ++ k)
  end.

Definition function_sought (T : table) (sc : scope) (k : string) : D :=
  match lookup sc k with
  | Some (VCode c) => oret (VCode c)
  | _ => stuck ("a function value that is not in scope: " ++ k)
  end.

(** ** Control *)

Definition while_ (T : table) (c body : D) : D :=
  Iter (fun _ : unit =>
    pbind c (fun o => match o with
      | Ok (VBool true) => pbind body (fun o' => turn o' (Ret (inl tt)))
      | Ok (VBool false) => Ret (inr (Ok VUnit))
      | Ok _ => pbind (stuck "a condition that gave no truth value") (fun o' => Ret (inr o'))
      | Exc x => Ret (inr (Exc x))
      | Brk v from => Ret (inr (Brk v from))
      end)) tt (fun r => Ret r).

Definition return_ (T : table) (v : val) (from : string) : D := Ret (Brk v from).
Definition rethrow (T : table) (x : exn) : D := othrow x.
Definition no_case (T : table) : D := othrow (Machine.Other "scala.MatchError").

(** `try`, with what handles what is thrown and what is run last (`Meaning.denote_step`, `Try`). *)
Definition try_ (T : table) (body : D) (handler : option (exn -> val -> D)) (last : option D) : D :=
  let after (o : outcome val) : D :=
    match last with
    | None => Ret o
    | Some f => pbind f (fun fo => match fo with Ok _ => Ret o | other => Ret other end)
    end in
  pbind body (fun o =>
    match o, handler with
    | Exc x, Some h => pbind (v <~ exn_val x ;; h x v) after
    | _, _ => after o
    end).

(** ** Patterns *)

Definition isa (T : table) (v : val) (t : ty) : D :=
  match instance T Library.supers v t with
  | Some b => oret (VBool b)
  | None => stuck "a pattern on a type that is not a class"
  end.

(** What an extractor gave, taken apart into the `n` parts its pattern has (`Meaning.pmatch_step`, `Unapply`):
    nothing, where it gave that the value is not taken. *)
Definition unapplied (T : table) (n : nat) (r : val) : X (option (list val)) :=
  let sized (xs : list val) : X (option (list val)) :=
    if Nat.eqb (List.length xs) n then oret (Some xs)
    else stuck "a pattern with more or fewer parts than the value" in
  match r with
  | VBool b => oret (if b then Some (repeat VUnit n) else None)
  | VObj (Data c xs) =>
      if String.eqb c "scala.None$" then oret None
      else if String.eqb c "scala.Some" then
        if Nat.eqb n 1
        then match xs with [_] => sized xs | _ => stuck "an extractor's result that does not fit the pattern" end
        else match xs with
             | [VObj (Data _ parts)] => sized parts
             | _ => stuck "an extractor's result that does not fit the pattern"
             end
      else sized xs
  | VObj (Ref _ _) => xs <~ components T r 1 n ;; sized xs
  | VList (x :: xs) => sized [x; VList xs]
  | _ => stuck "an extractor's result that is no option, no truth value and no product"
  end.

(** ** The programs of what is called *)

Definition program : Type := Machine.P code obj (Machine.res code obj).

(** The units staged of some code: a method by its definition, an initialiser by its class, a function and an
    argument taken unevaluated by the unit's name, which the value holds in the place of a body. *)
Record units := Units {
  u_method : sym -> option (val -> list val -> D);
  u_init : string -> option (val -> list val -> D);
  u_function : sym -> option (scope -> list val -> D);
  u_by_name : sym -> option (scope -> D) }.

(** What a call runs, where it was staged (`Meaning.interp`, with the unit in the place of the meaning of the
    tree). A method is found as `Meaning.run_method` finds it, by the object's class; one that was not staged
    is the meaning of its tree. *)
Definition method (T : table) (u : units) (s : sym) (arg : val) : option program :=
  match arg with
  | VList (VCode _ :: _) => None
  | VList (on :: args) =>
      match class_of_object on with
      | Some cls =>
          match impl T cls s with
          | Some d => option_map (fun f => leave (key (def_sym d)) (f on args)) (u_method u (def_sym d))
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition bodies (T : table) (u : units) (c : code) : option (val -> program) :=
  match c with
  | Method s => Some (fun arg =>
      match method T u s arg with
      | Some p => p
      | None => Meaning.interp T Outside.outside Library.supers c arg
      end)
  | Init cls => option_map (fun f arg =>
      match arg with
      | VList (this :: args) => leave "" (f this args)
      | _ => chaos_res "an initialiser called on no object"
      end) (u_init u cls)
  | Fn d sc _ =>
      match body_of d with
      | Some (Ident s) => option_map (fun f arg =>
          leave (key (def_sym d)) (f sc (match arg with VList vs => vs | _ => [] end))) (u_function u s)
      | _ => None
      end
  | Thunk (Ident s) sc => option_map (fun f _ => leave "" (f sc)) (u_by_name u s)
  | _ => None
  end.
