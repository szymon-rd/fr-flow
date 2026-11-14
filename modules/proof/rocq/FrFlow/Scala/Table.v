(** A program's classes and members, found by name: what the meaning of a call or of an object's making looks
    up. Built once from the trees of the program's files. *)

From Stdlib Require Import String List Bool.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Record table := Table {
  t_classes : list (string * tree);            (* each class, by its name *)
  t_members : list (sym * tree);               (* each value and method a class or an object declares *)
  t_lineage : list (string * list string);     (* each class with what it inherits from in the program *)
  t_modules : list (string * bool) }.          (* each object with state, and whether making it runs anything *)

Fixpoint assoc {A : Type} (xs : list (string * A)) (k : string) : option A :=
  match xs with
  | [] => None
  | (k', a) :: rest => if String.eqb k' k then Some a else assoc rest k
  end.

Fixpoint assoc_sym {A : Type} (xs : list (sym * A)) (s : sym) : option A :=
  match xs with
  | [] => None
  | (s', a) :: rest => if sym_eqb s' s then Some a else assoc_sym rest s
  end.

Definition class_of (T : table) (name : string) : option tree := assoc (t_classes T) name.
Definition member (T : table) (s : sym) : option tree := assoc_sym (t_members T) s.

(** ** A class's parts *)

Definition class_flags (c : tree) : list string := match c with ClassDef _ fs _ _ _ _ => fs | _ => [] end.
Definition class_body (c : tree) : list tree := match c with ClassDef _ _ _ _ _ body => body | _ => [] end.
Definition class_parents (c : tree) : list tree := match c with ClassDef _ _ _ ps _ _ => ps | _ => [] end.
Definition class_ctor (c : tree) : option tree := match c with ClassDef _ _ ctor _ _ _ => Some ctor | _ => None end.

(** The class a type names. *)
Fixpoint ty_class (t : ty) : option string :=
  match t with
  | TyRef name => Some name
  | TyApp c _ => ty_class c
  | TyAnnot u _ => ty_class u
  | TyLambda _ body => ty_class body
  | TyAlias _ named => ty_class named
  | _ => None
  end.

(** The type made by a constructor called, or named where a parent is only a type. *)
Fixpoint made (t : tree) : option ty :=
  match t with
  | Apply f _ | TypeApply f _ | Select f _ => made f
  | New type | TypeTree type => Some type
  | _ => None
  end.

Definition parent_names (c : tree) : list string :=
  flat_map (fun p => match made p with
    | Some type => match ty_class type with Some n => [n] | None => [] end
    | None => [] end) (class_parents c).

Fixpoint dedup (xs : list string) (seen : list string) : list string :=
  match xs with
  | [] => []
  | x :: rest => if existsb (String.eqb x) seen then dedup rest seen else x :: dedup rest (x :: seen)
  end.

(** A class and what it inherits from, itself first, the parent written last before those written earlier.
    `outside` gives what a class not of the program inherits from. *)
Fixpoint lineage (fuel : nat) (classes : list (string * tree)) (outside : string -> list string) (cls : string)
    : list string :=
  match fuel with
  | 0 => [cls]
  | S fuel' =>
      match assoc classes cls with
      | Some c => dedup (cls :: flat_map (lineage fuel' classes outside) (rev (parent_names c))) []
      | None => dedup (cls :: outside cls) []
      end
  end.

Definition ancestors (T : table) (outside : string -> list string) (cls : string) : list string :=
  lineage 12 (t_classes T) outside cls.

(** What a class inherits from in the program, itself first: kept in the table. *)
Definition own (T : table) (cls : string) : list string :=
  match assoc (t_lineage T) cls with Some line => line | None => [cls] end.

Definition inherits (T : table) (outside : string -> list string) (cls target : string) : bool :=
  existsb (String.eqb target) (ancestors T outside cls).

(** ** Members *)

Definition def_sym (d : tree) : sym :=
  match d with DefDef s _ _ _ _ _ | ValDef s _ _ _ => s | _ => NoSym end.
Definition def_flags (d : tree) : list string :=
  match d with DefDef _ fs _ _ _ _ | ValDef _ fs _ _ => fs | _ => [] end.
Definition def_name (d : tree) : string :=
  match def_sym d with Member _ n _ | Local n _ => n | NoSym => "" end.

(** The method of `c` that runs when `s` is called on an object of it: the one that is `s` or overrides it, and
    has a body. *)
Definition own_impl (c : tree) (s : sym) : option tree :=
  find (fun d => match d with
    | DefDef s' _ _ _ (Some _) overridden => sym_eqb s' s || known s overridden
    | _ => false end) (class_body c).

Fixpoint first_some {A B : Type} (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: rest => match f x with Some b => Some b | None => first_some f rest end
  end.

(** The body a call of `s` on an object of class `cls` runs: the nearest in what the class inherits from. *)
Definition impl (T : table) (cls : string) (s : sym) : option tree :=
  first_some (fun name => match class_of T name with Some c => own_impl c s | None => None end)
    (own T cls).

(** The member named `name` that an object of class `cls` has: the nearest. *)
Definition named (T : table) (cls name : string) : option tree :=
  first_some (fun n => match class_of T n with
    | Some c => find (fun d => String.eqb (def_name d) name) (class_body c)
    | None => None end) (own T cls).

(** A method's parameters, of every list, in order: each a `ValDef`. *)
Definition params (d : tree) : list tree :=
  match d with
  | DefDef _ _ paramss _ _ _ =>
      flat_map (fun ps => filter (fun p => match p with ValDef _ _ _ _ => true | _ => false end) ps) paramss
  | _ => []
  end.

Definition body_of (d : tree) : option tree :=
  match d with DefDef _ _ _ _ rhs _ => rhs | _ => None end.

(** Whether a parameter takes its argument unevaluated: passed by name, or `inline`. *)
Definition by_name (p : tree) : bool :=
  match p with
  | ValDef _ flags (TyByName _) _ => true
  | ValDef _ flags _ _ => flagged "Inline" flags
  | _ => false
  end.

(** ** Objects that are alone of their class

    An object (a Scala `object`) that has a value of its own, or a statement run when it is made, is an object
    of the heap, at a place fixed by its position among the program's objects: the place is there from the
    start, and the object is initialised when it is first used (`Meaning.module_obj`), as the JVM initialises a
    class. One with neither is a name. What a class it inherits from declares is its own. *)

Definition is_module (c : tree) : bool := flagged "Module" (class_flags c).

(** A value the class gives its objects, lazy or not. *)
Definition own_value (d : tree) : bool :=
  match d with ValDef _ flags _ (Some _) => negb (flagged "Module" flags) | _ => false end.

(** What an object of the class runs when it is made: a value that is not lazy, or a statement. *)
Definition own_initialiser (d : tree) : bool :=
  match d with
  | ValDef _ flags _ (Some _) => negb (flagged "Module" flags || flagged "Lazy" flags)
  | ValDef _ _ _ None | DefDef _ _ _ _ _ _ | ClassDef _ _ _ _ _ _ | TypeDef _ _ _ | Imported _ _ | Exported _ _ => false
  | _ => true
  end.

Definition inherited (classes : list (string * tree)) (line : list string) (what : tree -> bool) : bool :=
  existsb (fun name => match assoc classes name with
    | Some c => existsb what (class_body c)
    | None => false end) line.

Definition stateful_modules (T : table) : list string := map fst (t_modules T).

Definition needs_init (T : table) (cls : string) : bool :=
  match assoc (t_modules T) cls with Some runs => runs | None => false end.

Fixpoint index_of (xs : list string) (x : string) (i : nat) : option nat :=
  match xs with
  | [] => None
  | y :: rest => if String.eqb y x then Some i else index_of rest x (S i)
  end.

(** Where a module with state is: its place among them, from one. *)
Definition module_at (T : table) (cls : string) : option nat := index_of (stateful_modules T) cls 1.

(** ** The table of a program *)

Definition build (files : list tree) : table :=
  let all := over_list nodes files in
  let classes := flat_map (fun n => match n with ClassDef name _ _ _ _ _ => [(name, n)] | _ => [] end) all in
  let lines := map (fun c => (fst c, lineage 12 classes (fun _ => []) (fst c))) classes in
  Table classes
    (flat_map (fun n => match n with
       | ValDef (Member _ _ _ as s) _ _ _ | DefDef (Member _ _ _ as s) _ _ _ _ _ => [(s, n)]
       | _ => [] end) all)
    lines
    (flat_map (fun entry =>
       match assoc classes (fst entry) with
       | Some c =>
           if is_module c && inherited classes (snd entry) (fun d => own_value d || own_initialiser d)
           then [(fst entry, inherited classes (snd entry) own_initialiser)] else []
       | None => [] end) lines).
