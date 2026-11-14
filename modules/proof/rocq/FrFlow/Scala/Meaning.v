(** What Scala's trees mean: each form of tree as a program over the JDK's operations.

    `denote` gives a tree its program, in a scope of the variables around it. A call of a method is a call of
    the closure `Method`: which body runs is found when it is called (`interp`), from the class of what it is
    called on. So the meaning of a program's code is one function from its trees, said here once, and not a
    reading chosen construct by construct where the trees are read.

    What the code takes from outside the program (the JDK, Scala's library) is given by `outside`: for each
    definition, what a call of it does (`Library.v`). A form or a definition with no meaning here is `stuck`: it
    may do anything, so a proof passes it only where it is not reached, and a run stops at it. `Gaps.v` lists
    them for a program.

    One thing is not as the JVM has it: an object with values of its own (a module) is made before the program
    starts (`start`), where the JVM makes it when it is first used. *)

From Stdlib Require Import String List ZArith Bool Ascii.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope meaning_scope.

Definition cat (a b : string) : string := String.append a b.

(** A definition from outside the program: which of its arguments it takes unevaluated, and what a call does,
    given what the program says of values (`context`), what it is called on, its type arguments and its
    arguments. *)
Record context := Context {
  c_eq : val -> val -> X bool;              (* how two values are compared: `==` *)
  c_isa : val -> string -> option bool }.   (* whether a value is of a class *)

Record primitive := Prim {
  p_lazy : list bool;
  p_run : context -> val -> list ty -> list val -> X val }.

Section Meaning.

  Variable T : table.
  (** What a definition from outside does: by its owner and its name. *)
  Variable outside : string -> string -> option primitive.
  (** What a class from outside inherits from. *)
  Variable supers : string -> list string.

  Definition D : Type := X val.

  (** ** Values *)

  (** The class a value is of, when the code runs. *)
  Definition exn_class (x : exn) : string :=
    match x with
    | InterruptedException => "java.lang.InterruptedException"
    | ExecutionException _ => "java.util.concurrent.ExecutionException"
    | IllegalStateException => "java.lang.IllegalStateException"
    | IllegalThreadStateException => "java.lang.IllegalThreadStateException"
    | NullPointerException => "java.lang.NullPointerException"
    | NoSuchElementException => "java.util.NoSuchElementException"
    | Machine.Other c => c
    | Thrown _ => "java.lang.Throwable"
    end.

  Definition class_of_val (v : val) : option string :=
    match v with
    | VUnit => Some "scala.Unit"
    | VBool _ => Some "scala.Boolean"
    | VTid _ => Some "java.lang.Thread"
    | VExn x => Some (exn_class x)
    | VList [] => Some "scala.collection.immutable.Nil$"
    | VList _ => Some "scala.collection.immutable.::"
    | VObj (Ref c _) => Some c
    | VObj (Int _) => Some "scala.Int"
    | VObj (Long _) => Some "scala.Long"
    | VObj (Str _) | VObj Text => Some "java.lang.String"
    | VObj (Data c _) => Some c
    | VObj (Module m) => Some m
    | VObj (ClassOf _) => Some "java.lang.Class"
    | VObj Null | VCode _ => None
    end.

  Definition is_a (cls target : string) : bool :=
    String.eqb target "scala.Any" || String.eqb target "java.lang.Object" || String.eqb target "scala.AnyRef"
      || inherits T supers cls target.

  (** Whether a value is of a type, as far as the JVM can tell when the code runs: a type parameter is not
      tested. `None`: not known here. *)
  Fixpoint instance (v : val) (t : ty) : option bool :=
    match t with
    | TyRef name => match class_of_val v with
        | Some c => Some (is_a c name)
        | None => match v with VObj Null => Some false | _ => None end
        end
    | TyAlias _ named => instance v named
    | TyLambda _ body => instance v body
    | TyApp c _ => instance v c
    | TyAnnot u _ => instance v u
    | TyOr a b => match instance v a, instance v b with
        | Some x, Some y => Some (x || y)
        | _, _ => None
        end
    | TyAnd a b => match instance v a, instance v b with
        | Some x, Some y => Some (x && y)
        | _, _ => None
        end
    | _ => None
    end.

  (** Two values compared as data: `None` where it is for a method of the code to say (an object of a class
      with its own `equals`), or is not known (two functions). *)
  Fixpoint same_val (fuel : nat) (a b : val) : option bool :=
    match fuel with
    | 0 => None
    | S fuel' =>
        let all := fix all (xs ys : list val) : option bool :=
          match xs, ys with
          | [], [] => Some true
          | x :: xs', y :: ys' => match same_val fuel' x y with
              | Some true => all xs' ys'
              | other => other
              end
          | _, _ => Some false
          end in
        match a, b with
        | VUnit, VUnit => Some true
        | VBool x, VBool y => Some (Bool.eqb x y)
        | VTid x, VTid y => Some (Nat.eqb x y)
        | VExn x, VExn y => Some (if exn_eq_dec x y then true else false)
        | VList xs, VList ys => all xs ys
        | VObj (Int x), VObj (Int y) | VObj (Long x), VObj (Long y) => Some (Z.eqb x y)
        | VObj (Int x), VObj (Long y) | VObj (Long x), VObj (Int y) => Some (Z.eqb x y)
        | VObj (Str x), VObj (Str y) => Some (String.eqb x y)
        | VObj Null, VObj Null => Some true
        | VObj (Ref c r), VObj (Ref c' r') => if Nat.eqb r r' && String.eqb c c' then Some true else
            match named T c "equals" with Some _ => None | None => Some false end
        | VObj (Data c xs), VObj (Data c' ys) => if String.eqb c c' then all xs ys else Some false
        | VObj (Module m), VObj (Module m') => Some (String.eqb m m')
        | VObj (ClassOf c), VObj (ClassOf c') => Some (String.eqb c c')
        | VObj Text, _ | _, VObj Text | VCode _, _ | _, VCode _ => None
        | _, _ => Some false
        end
    end.

  (** `a == b`: the `equals` of `a`'s class where the code gives it one, else the comparison of data. *)
  Definition equal (a b : val) : X bool :=
    let plain := match same_val 64 a b with
      | Some r => oret r
      | None => stuck "two values compared that this meaning cannot compare"
      end in
    match a, b with
    | VObj (Ref c r), VObj (Ref c' r') =>
        if Nat.eqb r r' && String.eqb c c' then oret true else
        match named T c "equals" with
        | Some d => r <~ ocall (Method (def_sym d)) (VList [a; b]) ;;
            match r with VBool x => oret x | _ => stuck "equals gave no truth value" end
        | None => plain
        end
    | _, _ => plain
    end.

  (** ** Variables, objects, fields *)

  (** A lazy value read: its value, or `compute` run by the thread that is the first to read it; if that
      throws, the next read runs it again. *)
  Definition lazily (r : nat) (name : string) (what : once) (compute : D) : D :=
    x <~ oop (Enter r name what) ;;
    match x with
    | Some v => oret v
    | None => pbind compute (fun o => match o with
        | Ok v => _ <~ oop (ObjSet r name v) ;; oret v
        | other => pbind (oop (ObjSet r (entered name) VUnit)) (fun _ => Ret other)
        end)
    end.

  (** A variable read: a `var` is the object that holds it, a `lazy val` the object that holds it once it is
      evaluated, an argument passed by name is run. *)
  Definition read (e : scope) (k : string) : D :=
    match lookup e k with
    | Some (VObj (Ref c r)) =>
        if String.eqb c var_class then oop (ObjGet r var_field)
        else if String.eqb c lazy_class then
          lazily r lazy_field OfMethod (
            th <~ oop (ObjGet r thunk_field) ;;
            match th with VCode c => ocall c VUnit | _ => stuck "a lazy value with nothing that gives it" end)
        else oret (VObj (Ref c r))
    | Some (VCode (Thunk b sc)) => ocall (Thunk b sc) VUnit
    | Some v => oret v
    | None => stuck (cat "a variable that is not in scope: " k)
    end.

  (** The one object of a module's class: a place of the heap if it has state, else its name. *)
  Definition module_val (cls : string) : val :=
    match module_at T cls with Some r => vref cls r | None => VObj (Module cls) end.

  (** Where an object keeps that it is initialised. *)
  Definition init_field : string := "<init>".

  (** An object named. One that runs something when it is made is initialised by the first thread to name it,
      as the JVM initialises a class (JLS 12.4.2): a thread that names it meanwhile waits, the thread that
      initialises it sees it as it is so far. If its initialiser throws, that thread gets
      `ExceptionInInitializerError`, and every later naming `NoClassDefFoundError`. *)
  Definition module_obj (cls : string) : D :=
    match module_at T cls with
    | Some r =>
        if needs_init T cls then
          x <~ oop (Enter r init_field OfClass) ;;
          match x with
          | Some VUnit => oret (vref cls r)
          | Some _ => othrow (Machine.Other "java.lang.NoClassDefFoundError")
          | None =>
              Call (Init cls) (VList [vref cls r]) (fun made => match made with
                | inr _ => _ <~ oop (ObjSet r init_field VUnit) ;; oret (vref cls r)
                | inl _ =>
                    _ <~ oop (ObjSet r init_field (VBool false)) ;;
                    othrow (Machine.Other "java.lang.ExceptionInInitializerError")
                end)
          end
        else oret (vref cls r)
    | None => oret (VObj (Module cls))
    end.

  (** The fields an object of a class has when it is made, each with what the JVM gives a field not yet
      assigned: zero, false, or no object. A lazy value is no field until it is evaluated. *)
  Definition unset (t : ty) : val :=
    match ty_class t with
    | Some c =>
        if String.eqb c "scala.Int" || String.eqb c "scala.Short" || String.eqb c "scala.Byte"
           || String.eqb c "scala.Char" then vint 0
        else if String.eqb c "scala.Long" then vlong 0
        else if String.eqb c "scala.Boolean" then VBool false
        else if String.eqb c "scala.Unit" then VUnit
        else vnull
    | None => vnull
    end.

  Definition fields_of (cls : string) : list (string * val) :=
    flat_map (fun name => match class_of T name with
      | Some c => flat_map (fun d => match d with
          | ValDef _ flags t _ =>
              if flagged "Lazy" flags || flagged "Module" flags then [] else [(def_name d, unset t)]
          | _ => [] end) (class_body c)
      | None => [] end) (own T cls).

  (** `this` of the class `cls`. *)
  Definition this_val (e : scope) (cls : string) : D :=
    match class_of T cls with
    | Some c =>
        if is_module c then module_obj cls else
        match lookup e (this_key cls) with
        | Some v => oret v
        | None => stuck (cat "this, of a class the code is not in: " cls)
        end
    | None => stuck (cat "this, of a class that is not the program's: " cls)
    end.

  Definition get_field (v : val) (name : string) : D :=
    match v with
    | VObj (Ref _ r) => oop (ObjGet r name)
    | _ => stuck (cat "a field read of what is no object: " name)
    end.

  Definition set_field (v : val) (name : string) (x : val) : D :=
    match v with
    | VObj (Ref _ r) => _ <~ oop (ObjSet r name x) ;; oret VUnit
    | _ => stuck (cat "a field assigned of what is no object: " name)
    end.

  (** A class written inside a method: its objects keep the variables in scope where they are made. *)
  Definition is_local (cls : string) : bool :=
    existsb (fun a => Ascii.eqb a "#"%char) (list_ascii_of_string cls).

  (** ** Calls *)

  (** What a member is. *)
  Inductive kind :=
    | KMethod (d : tree)
    | KField (d : tree)
    | KLazy (d : tree)
    | KModule (cls : string)
    | KInner
    | KOutside.

  (** What declares a member is a package or an object: the member is one, not one for each object of a class. *)
  Definition static (owner : string) : bool :=
    match class_of T owner with Some c => is_module c | None => true end.

  Definition kind_of (s : sym) : kind :=
    match member T s with
    | Some (DefDef _ _ _ _ _ _ as d) => KMethod d
    | Some (ValDef _ flags t _ as d) =>
        if flagged "Module" flags then
          match s, ty_class t with
          | Member owner _ _, Some c => if static owner then KModule c else KInner
          | _, _ => KOutside
          end
        else if flagged "Lazy" flags then KLazy d else KField d
    | _ => KOutside
    end.

  (** The arguments of a call, each given as its tree and its program: one the callee takes unevaluated is its
      tree with the scope, the others are run in order. *)
  Fixpoint eval_args (e : scope) (lazy : list bool) (args : list (tree * D)) : X (list val) :=
    match args with
    | [] => oret []
    | (t, d) :: rest =>
        match lazy with
        | true :: lazy' => vs <~ eval_args e lazy' rest ;; oret (VCode (Thunk t e) :: vs)
        | _ :: lazy' => v <~ d ;; vs <~ eval_args e lazy' rest ;; oret (v :: vs)
        | [] => v <~ d ;; vs <~ eval_args e [] rest ;; oret (v :: vs)
        end
    end.

  Definition call_method (s : sym) (on : val) (args : list val) : D := ocall (Method s) (VList (on :: args)).

  (** A definition from outside: what `outside` says a call of it does. One that is only named (an object, a
      package: it has no signature) and has no meaning of its own is that name. *)
  Definition call_outside (s : sym) (on : D) (e : scope) (targs : list ty) (args : list (tree * D)) : D :=
    match s with
    | Member owner name signature =>
        match outside owner name with
        | Some p =>
            v <~ on ;; vs <~ eval_args e (p_lazy p) args ;;
            p_run p (Context equal (fun x cls => instance x (TyRef cls))) v targs vs
        | None =>
            match args with
            | [] =>
                if String.eqb signature "" || String.eqb signature "package"
                then oret (VObj (Module (cat owner (cat "." name))))
                else stuck (cat "a definition from outside with no meaning here: " (cat owner (cat "." name)))
            | _ => stuck (cat "a definition from outside with no meaning here: " (cat owner (cat "." name)))
            end
        end
    | _ => stuck "a definition from outside that is no member"
    end.

  (** What is said of every value, and so is no method of a class. *)
  Definition universal (name : string) (on : D) (e : scope) (targs : list ty) (args : list (tree * D))
      : option D :=
    let two (f : val -> val -> D) : D :=
      v <~ on ;; vs <~ eval_args e [] args ;;
      match vs with [w] => f v w | _ => stuck (cat "a comparison with other than one argument: " name) end in
    let truth (m : X bool) : D := b <~ m ;; oret (VBool b) in
    if String.eqb name "==" then Some (two (fun v w => truth (equal v w)))
    else if String.eqb name "!=" then Some (two (fun v w => truth (b <~ equal v w ;; oret (negb b))))
    else if String.eqb name "eq" then Some (two (fun v w => match same_val 1 v w with
      | Some b => oret (VBool b)
      | None => stuck "two objects compared for identity that this meaning cannot tell apart"
      end))
    else if String.eqb name "isInstanceOf" then Some (v <~ on ;; match targs with
      | [t] => match instance v t with
          | Some b => oret (VBool b)
          | None => stuck "a test of a type that is not a class"
          end
      | _ => stuck "isInstanceOf with other than one type"
      end)
    else if String.eqb name "asInstanceOf" || String.eqb name "$asInstanceOf$" then Some (v <~ on ;;
      match targs with
      | [t] => match instance v t with
          | Some false => match v with
              | VObj Null => oret v
              | _ => othrow (Machine.Other "java.lang.ClassCastException")
              end
          | _ => oret v
          end
      | _ => oret v
      end)
    else None.

  Definition is_universal (owner : string) : bool :=
    String.eqb owner "scala.Any" || String.eqb owner "java.lang.Object" || String.eqb owner "scala.AnyRef".

  (** The names `universal` gives a meaning. *)
  Definition universals : list string := ["=="; "!="; "eq"; "isInstanceOf"; "asInstanceOf"; "$asInstanceOf$"].

  (** A member selected of a value, and called with `args` if it is a method. *)
  Definition select_with (e : scope) (on : D) (s : sym) (targs : list ty) (args : list (tree * D)) : D :=
    match s with
    | Member owner name _ =>
        match kind_of s with
        | KMethod d =>
            v <~ on ;; vs <~ eval_args e (map by_name (params d)) args ;; call_method s v vs
        | KField d => v <~ on ;; get_field v name
        | KLazy d => v <~ on ;; call_method s v []
        | KModule c => module_obj c
        | KInner => stuck (cat "an object declared in a class, one for each object of the class: " name)
        | KOutside =>
            match (if is_universal owner then universal name on e targs args else None) with
            | Some m => m
            | None =>
                (* a method declared outside, called on an object of the program that has it *)
                v <~ on ;;
                match v with
                | VObj (Ref cls _) =>
                    match impl T cls s with
                    | Some d => vs <~ eval_args e (map by_name (params d)) args ;; call_method s v vs
                    | None => call_outside s (oret v) e targs args
                    end
                | _ => call_outside s (oret v) e targs args
                end
            end
        end
    | _ => stuck "a member that is no member"
    end.

  (** What a function made in the code is called with: the arguments of every list. *)
  Definition call_local (e : scope) (k : string) (args : list (tree * D)) : D :=
    match lookup e k with
    | Some (VCode (Fn d sc group)) =>
        vs <~ eval_args e (map by_name (params d)) args ;; ocall (Fn d sc group) (VList vs)
    | Some _ => stuck (cat "a call of what is no function: " k)
    | None => stuck (cat "a function that is not in scope: " k)
    end.

  (** A function made with no parameter list is called where it is named. *)
  Definition no_lists (d : tree) : bool :=
    match d with DefDef _ _ [] _ _ _ => true | _ => false end.

  (** A name on its own: a variable, a function of the code, or a member of the object the code is in. *)
  Definition ident_with (e : scope) (s : sym) (targs : list ty) (args : list (tree * D)) : D :=
    match s with
    | Local _ _ =>
        match args, lookup e (key s) with
        | [], Some (VCode (Fn d sc group)) =>
            if no_lists d then ocall (Fn d sc group) (VList []) else oret (VCode (Fn d sc group))
        | [], _ => read e (key s)
        | _, _ => call_local e (key s) args
        end
    | Member owner name _ =>
        match kind_of s with
        | KModule c => module_obj c
        | KOutside =>
            match (if is_universal owner then universal name (stuck "nothing to compare") e targs args
                   else None) with
            | Some m => m
            | None => call_outside s (oret VUnit) e targs args
            end
        | _ => select_with e (this_val e owner) s targs args
        end
    | NoSym => stuck "a name that names nothing"
    end.

  (** The arguments of a constructor called: of every list. *)
  Fixpoint spine_args (t : tree) : list tree :=
    match t with
    | Apply f args => spine_args f ++ args
    | TypeApply f _ => spine_args f
    | _ => []
    end.

  (** An object made: of a class of the program, a place of the heap, then the class's initialiser; of a class
      from outside, what `outside` says of its constructor. *)
  Definition construct (e : scope) (type : ty) (targs : list ty) (args : list (tree * D)) : D :=
    match ty_class type with
    | Some cls =>
        match class_of T cls with
        | Some c =>
            let ps := match class_ctor c with Some ctor => params ctor | None => [] end in
            vs <~ eval_args e (map by_name ps) args ;;
            r <~ oop (ObjNew cls (fields_of cls ++ if is_local cls then [(scope_field, scope_val e)] else [])) ;;
            _ <~ ocall (Init cls) (VList (vref cls r :: vs)) ;;
            oret (vref cls r)
        | None => call_outside (Member cls "<init>" "()") (oret VUnit) e targs args
        end
    | None => stuck "an object made of a type that is no class"
    end.

  (** A thrown exception as the value a handler is given: an object of a class of the program is its place. *)
  Definition exn_val (x : exn) : D :=
    match x with
    | Thrown r => cls <~ oop (ObjClass r) ;; oret (vref cls r)
    | _ => oret (VExn x)
    end.

  (** A component of a value taken apart by a pattern: of an object of the program, its member `_1`, `_2`, …. *)
  Definition component (v : val) (i : nat) : D :=
    match v with
    | VObj (Ref cls r) =>
        match named T cls (cat "_" (nat_text i)) with
        | Some (ValDef _ _ _ _ as d) => get_field v (def_name d)
        | Some (DefDef _ _ _ _ _ _ as d) => call_method (def_sym d) v []
        | _ => stuck "an object taken apart that has no such part"
        end
    | _ => stuck "a value taken apart that is no object"
    end.

  Fixpoint components (v : val) (from count : nat) : X (list val) :=
    match count with
    | 0 => oret []
    | S count' => x <~ component v from ;; xs <~ components v (S from) count' ;; oret (x :: xs)
    end.

  (** One turn of a loop gives what ends it, or goes round. *)
  Definition turn (o : outcome val) (next : Machine.P code obj (unit + outcome val)) : Machine.P code obj (unit + outcome val) :=
    match o with
    | Ok _ => next
    | Exc x => Ret (inr (Exc x))
    | Brk v from => Ret (inr (Brk v from))
    end.

  (** ** The meaning of a tree *)

  Fixpoint denote (e : scope) (t : tree) {struct t} : D :=
    (* the statements of a block, in order, then what follows them in the scope they leave *)
    let block := fix block (e : scope) (stats : list tree) (k : scope -> D) {struct stats} : D :=
      match stats with
      | [] => k e
      | st :: rest =>
          match st with
          | ValDef s flags _ (Some rhs) =>
              if flagged "Lazy" flags then
                r <~ oop (ObjNew lazy_class []) ;;
                let e' := (key s, vref lazy_class r) :: e in
                _ <~ oop (ObjSet r thunk_field (VCode (Thunk rhs e'))) ;; block e' rest k
              else
              v <~ denote e rhs ;;
              if flagged "Mutable" flags then
                r <~ oop (ObjNew var_class [(var_field, v)]) ;; block ((key s, vref var_class r) :: e) rest k
              else block ((key s, v) :: e) rest k
          | ValDef s _ _ None => stuck (cat "a value with no right side: " (key s))
          | DefDef s _ _ _ _ _ =>
              block ((key s, VCode (Fn st e (filter (fun d => match d with
                | DefDef _ _ _ _ _ _ => true
                | _ => false end) (st :: rest)))) :: e) rest k
          | ClassDef _ _ _ _ _ _ | TypeDef _ _ _ | Imported _ _ | Exported _ _ => block e rest k
          | other => _ <~ denote e other ;; block e rest k
          end
      end in
    match t with
    | Literal c =>
        match of_const c with Some v => oret v | None => stuck "a floating-point constant" end
    | Ident s => ident_with e s [] []
    | Select on s => select_with e (denote e on) s [] []
    | This cls => this_val e cls
    | Apply f args => applied e f [] ((fix each (ts : list tree) : list (tree * D) :=
        match ts with [] => [] | a :: rest => (a, denote e a) :: each rest end) args)
    | TypeApply f targs => applied e f targs []
    | Typed x _ | NamedArg _ x => denote e x
    | Block stats result => block e stats (fun e' => denote e' result)
    | Inlined _ bindings body => block e bindings (fun e' => denote e' body)
    | If c a b =>
        v <~ denote e c ;;
        match v with
        | VBool true => denote e a
        | VBool false => denote e b
        | _ => stuck "a condition that gave no truth value"
        end
    | While c body =>
        Iter (fun _ : unit =>
          pbind (denote e c) (fun o => match o with
            | Ok (VBool true) => pbind (denote e body) (fun o' => turn o' (Ret (inl tt)))
            | Ok (VBool false) => Ret (inr (Ok VUnit))
            | Ok _ => pbind (stuck "a condition that gave no truth value") (fun o' => Ret (inr o'))
            | Exc x => Ret (inr (Exc x))
            | Brk v from => Ret (inr (Brk v from))
            end)) tt (fun r => Ret r)
    | Assign (Ident s) rhs =>
        match s with
        | Local _ _ =>
            match lookup e (key s) with
            | Some (VObj (Ref _ r)) => v <~ denote e rhs ;; _ <~ oop (ObjSet r var_field v) ;; oret VUnit
            | _ => stuck (cat "an assignment to what is no variable: " (key s))
            end
        | Member owner name _ => on <~ this_val e owner ;; v <~ denote e rhs ;; set_field on name v
        | NoSym => stuck "an assignment to nothing"
        end
    | Assign (Select on (Member _ name _)) rhs =>
        o <~ denote e on ;; v <~ denote e rhs ;; set_field o name v
    | Assign _ _ => stuck "an assignment to what is neither a variable nor a field"
    | Match _ on cases =>
        v <~ denote e on ;;
        (fix try (cs : list tree) : D :=
          match cs with
          | [] => othrow (Machine.Other "scala.MatchError")
          | CaseDef p guard body :: rest =>
              m <~ pmatch e p v ;;
              match m with
              | None => try rest
              | Some e' =>
                  match guard with
                  | None => denote e' body
                  | Some g =>
                      b <~ denote e' g ;;
                      match b with
                      | VBool true => denote e' body
                      | VBool false => try rest
                      | _ => stuck "a guard that gave no truth value"
                      end
                  end
              end
          | _ :: _ => stuck "a case that is no case"
          end) cases
    | Try body cases finalizer =>
        let after (o : outcome val) : D :=
          match finalizer with
          | None => Ret o
          | Some f => pbind (denote e f) (fun fo => match fo with Ok _ => Ret o | other => Ret other end)
          end in
        pbind (denote e body) (fun o =>
          match o with
          | Exc x =>
              pbind (v <~ exn_val x ;;
                (fix try (cs : list tree) : D :=
                  match cs with
                  | [] => othrow x
                  | CaseDef p guard handler :: rest =>
                      m <~ pmatch e p v ;;
                      match m with
                      | None => try rest
                      | Some e' =>
                          match guard with
                          | None => denote e' handler
                          | Some g =>
                              b <~ denote e' g ;;
                              match b with
                              | VBool true => denote e' handler
                              | VBool false => try rest
                              | _ => stuck "a guard that gave no truth value"
                              end
                          end
                      end
                  | _ :: _ => stuck "a handler that is no case"
                  end) cases) after
          | _ => after o
          end)
    | Return x from => v <~ denote e x ;; Ret (Brk v (key from))
    | Closure (Ident s) _ =>
        match lookup e (key s) with
        | Some (VCode c) => oret (VCode c)
        | _ => stuck (cat "a function value that is not in scope: " (key s))
        end
    | Repeated elems _ =>
        vs <~ (fix each (ts : list tree) : X (list val) :=
          match ts with
          | [] => oret []
          | a :: rest => v <~ denote e a ;; vs <~ each rest ;; oret (v :: vs)
          end) elems ;;
        oret (VList vs)
    | New _ => stuck "a class made with no constructor called"
    | Super _ _ => stuck "a member of a parent, called past this class's own"
    | SelectOuter _ _ _ => stuck "a member of an enclosing object, reached from inside"
    | SummonFrom _ => stuck "a choice made by the compiler where the code is inlined"
    | Closure _ _ => stuck "a function value of what is no function made here"
    | _ => stuck "a tree that is no expression"
    end

  (** A call: `f` with the type arguments and the arguments given to it so far. *)
  with applied (e : scope) (f : tree) (targs : list ty) (args : list (tree * D)) {struct f} : D :=
    match f with
    | Apply g more => applied e g targs ((fix each (ts : list tree) : list (tree * D) :=
        match ts with [] => [] | a :: rest => (a, denote e a) :: each rest end) more ++ args)
    | TypeApply g ts => applied e g ts args
    | Select (New type) _ => construct e type targs args
    | Select on s => select_with e (denote e on) s targs args
    | Ident s => ident_with e s targs args
    | Typed g _ => applied e g targs args
    | _ => stuck "a call of what is neither a name nor a member"
    end

  (** Whether a value is what a pattern takes, and the variables the pattern then binds. *)
  with pmatch (e : scope) (p : tree) (v : val) {struct p} : X (option scope) :=
    match p with
    | Wildcard => oret (Some e)
    | Bind s inner =>
        m <~ pmatch e inner v ;;
        oret (match m with Some e' => Some ((key s, v) :: e') | None => None end)
    | Literal c =>
        match of_const c with
        | Some cv => b <~ equal v cv ;; oret (if b then Some e else None)
        | None => stuck "a floating-point constant in a pattern"
        end
    | TypeTest inner type | Typed inner type =>
        match instance v type with
        | Some true => pmatch e inner v
        | Some false => oret None
        | None => stuck "a pattern on a type that is not a class"
        end
    | Alternatives ps =>
        (fix any (qs : list tree) : X (option scope) :=
          match qs with
          | [] => oret None
          | q :: rest => m <~ pmatch e q v ;; match m with Some _ => oret (Some e) | None => any rest end
          end) ps
    | Unapply f _ ps =>
        r <~ applied e f [] [(Wildcard, oret v)] ;;
        let zip := fix zip (qs : list tree) (xs : list val) (e' : scope) : X (option scope) :=
          match qs, xs with
          | [], [] => oret (Some e')
          | q :: qs', x :: xs' =>
              m <~ pmatch e' q x ;; match m with Some e'' => zip qs' xs' e'' | None => oret None end
          | _, _ => stuck "a pattern with more or fewer parts than the value"
          end in
        match r with
        | VBool b => oret (if b then Some e else None)
        | VObj (Data c xs) =>
            if String.eqb c "scala.None$" then oret None
            else if String.eqb c "scala.Some" then
              match ps, xs with
              | [_], [_] => zip ps xs e
              | _, [VObj (Data _ parts)] => zip ps parts e
              | _, _ => stuck "an extractor's result that does not fit the pattern"
              end
            else zip ps xs e
        | VObj (Ref _ _) => xs <~ components r 1 (List.length ps) ;; zip ps xs e
        | VList (x :: xs) => zip ps [x; VList xs] e
        | _ => stuck "an extractor's result that is no option, no truth value and no product"
        end
    | Ident s => x <~ ident_with e s [] [] ;; b <~ equal v x ;; oret (if b then Some e else None)
    | Select on s =>
        x <~ select_with e (denote e on) s [] [] ;; b <~ equal v x ;; oret (if b then Some e else None)
    | _ => stuck "a pattern of a form with no meaning here"
    end.

  (** ** What a closure runs *)

  Definition chaos_res (why : string) : Machine.P code obj (Machine.res code obj) :=
    Vis (Chaos (Machine.res code obj) why) (fun r => Ret r).

  (** A body's outcome as what a call gives: its value, or what it threw; a `return` ends the method it is of. *)
  Definition leave (k : string) (m : D) : Machine.P code obj (Machine.res code obj) :=
    pbind m (fun o => match o with
      | Ok v => Ret (inr v)
      | Exc x => Ret (inl x)
      | Brk v from => if String.eqb from k then Ret (inr v) else chaos_res "a return out of another method"
      end).

  Definition bind_params (ps : list tree) (args : list val) : scope :=
    combine (map (fun p => key (def_sym p)) ps) args.

  (** The functions made in one block: each may call the others. *)
  Definition group_scope (group : list tree) (sc : scope) : scope :=
    map (fun d => (key (def_sym d), VCode (Fn d sc group))) group.

  Definition this_scope (cls : string) (on : val) : scope :=
    map (fun a => (this_key a, on)) (own T cls).

  (** The variables an object of a class written inside a method was made among. *)
  Definition captured (on : val) : X scope :=
    match on with
    | VObj (Ref cls r) => if is_local cls then v <~ oop (ObjGet r scope_field) ;; oret (val_scope v) else oret []
    | _ => oret []
    end.

  Definition class_of_object (on : val) : option string :=
    match on with VObj (Ref c _) => Some c | VObj (Module m) => Some m | _ => None end.

  Definition run_method (s : sym) (on : val) (args : list val) : Machine.P code obj (Machine.res code obj) :=
    match on with
    | VCode f => Call f (VList args) (fun r => Ret r)      (* a function used as an object with one method *)
    | _ =>
        match class_of_object on with
        | Some cls =>
            match impl T cls s with
            | Some d =>
                match body_of d with
                | Some b => leave (key (def_sym d))
                    (sc <~ captured on ;; denote (bind_params (params d) args ++ this_scope cls on ++ sc) b)
                | None => chaos_res "a method with no body"
                end
            | None =>
                (* a value of the class is what the member is: read, and if it is lazy evaluated once *)
                let name := match s with Member _ n _ => n | _ => "" end in
                match named T cls name, on with
                | Some (ValDef _ flags _ (Some rhs)), VObj (Ref _ r) =>
                    if flagged "Lazy" flags then
                      leave "" (sc <~ captured on ;; lazily r name OfMember (denote (this_scope cls on ++ sc) rhs))
                    else leave "" (get_field on name)
                | Some (ValDef _ _ _ None), _ => leave "" (get_field on name)
                | _, _ => chaos_res (cat "a method the object's class does not have: " (key s))
                end
            end
        | None => chaos_res (cat "a method of the program called on what is no object of it: " (key s))
        end
    end.

  (** What making an object of `cls` runs on it: its constructor's parameters become its fields, each parent of
      the program is initialised, then the values and statements of its body, in order. *)
  Definition init (cls : string) (this : val) (args : list val) : Machine.P code obj (Machine.res code obj) :=
    match class_of T cls with
    | Some c =>
        let ps := match class_ctor c with Some ctor => params ctor | None => [] end in
        leave "" (
          sc0 <~ captured this ;;
          let sc := bind_params ps args ++ this_scope cls this ++ sc0 in
          _ <~ oeach (fun d => match d with
            | ValDef s flags _ None =>
                if flagged "ParamAccessor" flags then
                  match lookup (combine (map def_name ps) args) (def_name d) with
                  | Some v => set_field this (def_name d) v
                  | None => oret VUnit
                  end
                else oret VUnit
            | _ => oret VUnit end) (class_body c) ;;
          _ <~ oeach (fun p => match made p with
            | Some type => match ty_class type with
                | Some pc => match class_of T pc with
                    | Some _ => vs <~ oeach (denote sc) (spine_args p) ;; ocall (Init pc) (VList (this :: vs))
                    | None => oret VUnit
                    end
                | None => oret VUnit
                end
            | None => oret VUnit end) (class_parents c) ;;
          _ <~ oeach (fun st => match st with
            | ValDef s flags _ (Some rhs) =>
                if flagged "Lazy" flags || flagged "Module" flags then oret VUnit
                else v <~ denote sc rhs ;; set_field this (def_name st) v
            | ValDef _ _ _ None | DefDef _ _ _ _ _ _ | ClassDef _ _ _ _ _ _ | TypeDef _ _ _ | Imported _ _
            | Exported _ _ => oret VUnit
            | other => denote sc other end) (class_body c) ;;
          oret VUnit)
    | None => chaos_res (cat "an object made of a class that is not the program's: " cls)
    end.

  Definition interp (c : code) (arg : val) : Machine.P code obj (Machine.res code obj) :=
    match c with
    | Fn d sc group =>
        let args := match arg with VList vs => vs | _ => [] end in
        match body_of d with
        | Some b => leave (key (def_sym d)) (denote (bind_params (params d) args ++ group_scope group sc ++ sc) b)
        | None => chaos_res "a function with no body"
        end
    | Thunk b sc => leave "" (denote sc b)
    | Method s =>
        match arg with
        | VList (on :: args) => run_method s on args
        | _ => chaos_res "a method called on nothing"
        end
    | Bound s on => run_method s on []
    | Init cls =>
        match arg with
        | VList (this :: args) => init cls this args
        | _ => chaos_res "an initialiser run on nothing"
        end
    end.

End Meaning.
