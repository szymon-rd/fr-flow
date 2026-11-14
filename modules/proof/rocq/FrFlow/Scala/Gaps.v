(** What the meaning of a program stops at, found without running it.

    `Meaning.denote` gives a tree a program, or `stuck` where it has none to give: a run that reaches one stops
    (`Run.Stopped`), and a proof about a program that may reach one proves nothing of what follows it. This
    file lists, for a set of definitions, where that can happen for a reason that shows in the tree itself:

    - a form of tree `denote` has no meaning for (`halts`);
    - an argument given by name that is not where the parameter of that name is (`misplaced`): the meaning
      takes arguments in the order written, which is the order of the parameters in every call the compiler
      typed, and this checks it;
    - a definition taken from outside the program that the library gives no meaning (`unmeant`);
    - an object or a class declared inside a class: the meaning does not give an object the object it was made
      in (`inner`).

    What does not show in a tree is not here: a value of the wrong kind at a call, a type test on a type that is
    no class. Those show when the program is run (`Run`). *)

From Stdlib Require Import String List Bool Ascii.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** The form of one node, if `denote` stops at it wherever it stands. *)
Definition halt (t : tree) : option string :=
  match t with
  | Literal c => match of_const c with Some _ => None | None => Some "a floating-point constant" end
  | Super _ _ => Some "Super"
  | SelectOuter _ _ _ => Some "SelectOuter"
  | SummonFrom _ => Some "SummonFrom"
  | Closure (Ident _) _ => None
  | Closure _ _ => Some "Closure"
  | Assign (Ident _) _ | Assign (Select _ (Member _ _ _)) _ => None
  | Assign _ _ => Some "Assign"
  | Other _ _ => Some "Other"
  | _ => None
  end.

(** Each definition among `defs` with a node the meaning stops at, and the forms. *)
Definition halts (T : table) (defs : list sym) : list (sym * list string) :=
  flat_map (fun s => match member T s with
    | Some d =>
        match flat_map (fun n => match halt n with Some w => [w] | None => [] end) (nodes d) with
        | [] => []
        | found => [(s, found)]
        end
    | None => [] end) defs.

(** What is called, and how many arguments it has been given already. *)
Fixpoint callee (f : tree) : option sym * nat :=
  match f with
  | Apply g args => let (s, n) := callee g in (s, n + List.length args)
  | TypeApply g _ | Typed g _ => callee g
  | Select _ s | Ident s => (Some s, 0)
  | _ => (None, 0)
  end.

(** Whether each argument given by name is where the parameter of that name is. *)
Fixpoint placed (ps : list tree) (args : list tree) : bool :=
  match args, ps with
  | [], _ => true
  | NamedArg name _ :: rest, p :: ps' => String.eqb (def_name p) name && placed ps' rest
  | NamedArg _ _ :: _, [] => false
  | _ :: rest, _ :: ps' => placed ps' rest
  | _ :: rest, [] => placed [] rest
  end.

Definition by_name_given (args : list tree) : bool :=
  existsb (fun a => match a with NamedArg _ _ => true | _ => false end) args.

(** Each definition among `defs` with a call that gives an argument by name out of its place, or to a
    definition whose parameters are not the program's to see. *)
Definition misplaced (T : table) (defs : list sym) : list sym :=
  filter (fun s => match member T s with
    | Some d => existsb (fun n => match n with
        | Apply f args =>
            by_name_given args && match callee f with
              | (Some c, given) => match member T c with
                  | Some target => negb (placed (skipn given (params target)) args)
                  | None => true
                  end
              | (None, _) => true
              end
        | _ => false end) (nodes d)
    | None => false end) defs.

(** The definitions from outside, among `used`, that have no meaning: one the library gives none; that is not
    said of every value (`Meaning.universal`); that no class of the program has a method for (a call of it on
    an object of the program runs that method); and that is not only a name (an object, a package: it has no
    signature). *)
Definition unmeant (T : table) (outside : string -> string -> option primitive) (used : list sym) : list sym :=
  filter (fun s => match s with
    | Member owner name signature =>
        match outside owner name with
        | Some _ => false
        | None =>
            negb (String.eqb signature "" || String.eqb signature "package"
              || (is_universal owner && existsb (String.eqb name) universals)
              || existsb (fun c => match own_impl (snd c) s with Some _ => true | None => false end)
                   (t_classes T))
        end
    | _ => false end) used.

(** What declares `name`: the part before its last dot. *)
Definition declarer (name : string) : string :=
  let fix upto (chars : list Ascii.ascii) (last : nat) (i : nat) : nat :=
    match chars with
    | [] => last
    | c :: rest => upto rest (if Ascii.eqb c "."%char then i else last) (S i)
    end in
  substring 0 (upto (list_ascii_of_string name) 0 0) name.

(** The classes and objects declared in a class that is no object: each belongs to one object of that class.
    One written inside a method is not among them: it keeps the variables it was made among. *)
Definition inner (T : table) : list string :=
  flat_map (fun c => match class_of T (declarer (fst c)) with
    | Some owner => if is_module owner || is_local (fst c) then [] else [fst c]
    | None => [] end) (t_classes T).
