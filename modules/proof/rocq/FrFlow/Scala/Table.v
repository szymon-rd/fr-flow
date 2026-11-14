(** A program's classes and members, found by name: what the meaning of a call or of an object's making looks
    up. Built once from the trees of the program's files. *)

From Stdlib Require Import String List Bool.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** The definitions of some files (each class by its name; each value and method a class or an object declares;
    each class with what it inherits from in the program; each object with state, and whether making it runs
    anything), or those of one program and then of another, linked after it. *)
Inductive table :=
  | Table (classes : list (string * tree)) (members : list (sym * tree))
      (lines : list (string * list string)) (modules : list (string * bool))
  | Extend (T more : table).

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

(** A name no program defines: one inside `java`, `javax` or `scala`, or the compiler's own. The meaning never
    looks such a name up among a program's definitions: so what a call of the JDK or a test on one of its
    classes means does not depend on the program, and what a program's own names mean does not depend on what
    is defined after them (`extend`). *)
Definition foreign (name : string) : bool :=
  within "java" name || within "javax" name || within "scala" name || String.eqb name "<special-ops>".

(** A lookup in a program linked after another finds what the first defines first: so what the first defines
    means what it meant, whatever is linked after it. A lookup names the tables it reads and copies nothing of
    them, which keeps a proof that computes one small. *)
Fixpoint class_in (T : table) (name : string) : option tree :=
  match T with
  | Table classes _ _ _ => assoc classes name
  | Extend T' more => match class_in T' name with Some c => Some c | None => class_in more name end
  end.

Fixpoint member_in (T : table) (s : sym) : option tree :=
  match T with
  | Table _ members _ _ => assoc_sym members s
  | Extend T' more => match member_in T' s with Some d => Some d | None => member_in more s end
  end.

Fixpoint line_in (T : table) (cls : string) : option (list string) :=
  match T with
  | Table _ _ lines _ => assoc lines cls
  | Extend T' more => match line_in T' cls with Some l => Some l | None => line_in more cls end
  end.

Fixpoint modules_of (T : table) : list (string * bool) :=
  match T with
  | Table _ _ _ modules => modules
  | Extend T' more => modules_of T' ++ modules_of more
  end.

Fixpoint classes_of (T : table) : list (string * tree) :=
  match T with
  | Table classes _ _ _ => classes
  | Extend T' more => classes_of T' ++ classes_of more
  end.

Definition class_of (T : table) (name : string) : option tree :=
  if foreign name then None else class_in T name.
Definition member (T : table) (s : sym) : option tree :=
  match s with
  | Member owner _ _ => if foreign owner then None else member_in T s
  | _ => None
  end.

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
Fixpoint lineage (fuel : nat) (found : string -> option tree) (cls : string) : list string :=
  match fuel with
  | 0 => [cls]
  | S fuel' =>
      match found cls with
      | Some c => dedup (cls :: flat_map (lineage fuel' found) (rev (parent_names c))) []
      | None => [cls]
      end
  end.

(** What a class inherits from in the program, itself first, and the classes from outside those inherit from
    directly: kept in the table. *)
Definition own (T : table) (cls : string) : list string :=
  if foreign cls then [cls] else match line_in T cls with Some line => line | None => [cls] end.

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

Definition inherited (found : string -> option tree) (line : list string) (what : tree -> bool) : bool :=
  existsb (fun name => match found name with
    | Some c => existsb what (class_body c)
    | None => false end) line.

Definition stateful_modules (T : table) : list string := map fst (modules_of T).

Fixpoint module_in (T : table) (cls : string) : option bool :=
  match T with
  | Table _ _ _ modules => assoc modules cls
  | Extend T' more => match module_in T' cls with Some runs => Some runs | None => module_in more cls end
  end.

Definition needs_init (T : table) (cls : string) : bool :=
  if foreign cls then false else match module_in T cls with Some runs => runs | None => false end.

Fixpoint index_of (xs : list string) (x : string) (i : nat) : option nat :=
  match xs with
  | [] => None
  | y :: rest => if String.eqb y x then Some i else index_of rest x (S i)
  end.

(** The place of an object with state among the program's, counted from `from`: those of a program linked
    after another come after the other's. *)
Fixpoint module_from (T : table) (cls : string) (from : nat) : option nat :=
  match T with
  | Table _ _ _ modules => index_of (map fst modules) cls from
  | Extend T' more =>
      match module_from T' cls from with
      | Some r => Some r
      | None => module_from more cls (from + List.length (modules_of T'))
      end
  end.

(** Where a module with state is: its place among them, from one. *)
Definition module_at (T : table) (cls : string) : option nat :=
  if foreign cls then None else module_from T cls 1.

(** ** The table of a program *)

(** The definitions of `files`, in a program that has those of `base` before them. *)
Definition build_after (base : table) (files : list tree) : table :=
  let all := over_list nodes files in
  let classes := flat_map (fun n => match n with ClassDef name _ _ _ _ _ => [(name, n)] | _ => [] end) all in
  let found := fun name => match class_in base name with Some c => Some c | None => assoc classes name end in
  let lines := map (fun c => (fst c, lineage 12 found (fst c))) classes in
  Table classes
    (flat_map (fun n => match n with
       | ValDef (Member _ _ _ as s) _ _ _ | DefDef (Member _ _ _ as s) _ _ _ _ _ => [(s, n)]
       | _ => [] end) all)
    lines
    (flat_map (fun entry =>
       match assoc classes (fst entry) with
       | Some c =>
           if is_module c && inherited found (snd entry) (fun d => own_value d || own_initialiser d)
           then [(fst entry, inherited found (snd entry) own_initialiser)] else []
       | None => [] end) lines).

Definition build (files : list tree) : table := build_after (Table [] [] [] []) files.

(** A program that uses another: the other's definitions, then its own. *)
Definition extend (T more : table) : table := Extend T more.
