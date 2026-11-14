(** A program: the trees of its files. What it defines, what it refers to, and so what it takes from outside.

    A proof about code read from a jar rests on what that code calls and does not define: the JDK, Scala's
    library, another library. `outside` is that list, computed from the trees, so that it is known whole: each
    entry is a definition whose behaviour the proofs must assume (a contract) or must not depend on. `undefined`
    is what the code refers to inside its own package and does not define; where it is empty, the trees are the
    whole of the code. *)

From Stdlib Require Import String List Bool.
Require Import FrFlow.Scala.Tree.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition sym_eqb (a b : sym) : bool :=
  match a, b with
  | NoSym, NoSym => true
  | Member o n s, Member o' n' s' => String.eqb n n' && String.eqb s s' && String.eqb o o'
  | Local n i, Local n' i' => String.eqb n n' && Nat.eqb i i'
  | _, _ => false
  end.

Definition known (s : sym) (among : list sym) : bool := existsb (sym_eqb s) among.

Fixpoint distinct (ss : list sym) : list sym :=
  match ss with
  | [] => []
  | s :: rest => if known s rest then distinct rest else s :: distinct rest
  end.

(** What `f` gives of each tree of a list, in order. *)
Definition over_list {A : Type} (f : tree -> list A) : list tree -> list A :=
  fix go ts := match ts with [] => [] | t :: rest => f t ++ go rest end.

(** Every tree inside a tree, itself first: the one traversal, which every reading below filters. An import is
    not gone into: it is no code. *)
Fixpoint nodes (t : tree) : list tree :=
  let many := fix go ts := match ts with [] => [] | x :: rest => nodes x ++ go rest end in
  let maybe := fun o => match o with Some x => nodes x | None => [] end in
  t :: match t with
  | Select q _ | SelectOuter q _ _ | Super q _ | TypeApply q _ | NamedArg _ q | Typed q _ | Closure q _
  | Return q _ | Bind _ q | TypeTest q _ => nodes q
  | Apply f args => nodes f ++ many args
  | Assign l r | While l r => nodes l ++ nodes r
  | Block stats result => many stats ++ nodes result
  | If c a b => nodes c ++ nodes a ++ nodes b
  | Match _ on cases => nodes on ++ many cases
  | SummonFrom cases | Alternatives cases => many cases
  | Try body cases fin => nodes body ++ many cases ++ maybe fin
  | Repeated elems _ => many elems
  | Inlined call bindings body => maybe call ++ many bindings ++ nodes body
  | ValDef _ _ _ rhs => maybe rhs
  | DefDef _ _ paramss _ rhs _ =>
      (fix go pss := match pss with [] => [] | ps :: rest => many ps ++ go rest end) paramss ++ maybe rhs
  | ClassDef _ _ ctor parents self body => nodes ctor ++ many parents ++ maybe self ++ many body
  | PackageClause _ stats => many stats
  | CaseDef p guard body => nodes p ++ maybe guard ++ nodes body
  | Unapply f givens ps => nodes f ++ many givens ++ many ps
  | _ => []
  end.

(** The members a tree defines: the values and methods a class or an object declares. *)
Definition defines (t : tree) : list sym :=
  flat_map (fun n => match n with
    | ValDef (Member _ _ _ as s) _ _ _ | DefDef (Member _ _ _ as s) _ _ _ _ _ => [s]
    | _ => [] end) (nodes t).

(** The definitions a tree refers to: every name it reads, selects or calls. *)
Definition mentions (t : tree) : list sym :=
  flat_map (fun n => match n with Ident s | Select _ s => [s] | _ => [] end) (nodes t).

(** `name` is `package`, or inside it. *)
Definition within (package name : string) : bool :=
  String.eqb name package || String.prefix (package ++ ".")%string name.

(** A definition of `package`'s code: a member whose owner is inside it. A package, or a definition made inside
    a method, is not one. *)
Definition inside (package : string) (s : sym) : bool :=
  match s with
  | Member owner _ signature => within package owner && negb (String.eqb signature "package")
  | _ => false
  end.

Definition outsider (package : string) (s : sym) : bool :=
  match s with
  | Member owner _ signature => negb (within package owner) && negb (String.eqb signature "package")
  | _ => false
  end.

Section Program.

  Variable package : string.
  Variable files : list tree.

  Definition defined : list sym := over_list defines files.
  Definition mentioned : list sym := over_list mentions files.

  (** What the code refers to in its own package and does not define. *)
  Definition undefined : list sym :=
    filter (fun s => negb (known s defined)) (distinct (filter (inside package) mentioned)).

  (** What the code takes from outside its package: the surface every proof about it rests on. *)
  Definition outside : list sym := distinct (filter (outsider package) mentioned).

End Program.

(** Two lists name the same definitions. *)
Definition same (a b : list sym) : bool :=
  forallb (fun s => known s b) a && forallb (fun s => known s a) b.

(** ** What a part of a program reaches

    The definitions that may run when some of them are called: what their bodies refer to, and so on. A method
    that may be called is taken to reach every method that overrides it (any object may be the one called), and
    making an object is taken to reach each of its methods that overrides one from outside the package (code
    outside may call it back). So `reaches` is at least what runs; it may hold more. *)

Record entry := Entry { e_sym : sym; e_calls : list sym; e_overrides : list sym }.

Section Reach.

  Variable package : string.
  Variable files : list tree.

  (** What making an object of a class runs: its parents' constructors, the statements and the values' right
      sides of its body; and the methods code outside may call on it. *)
  Definition constructs (parents body : list tree) : list sym :=
    over_list mentions parents ++ flat_map (fun s => match s with
      | DefDef m _ _ _ _ overridden => if existsb (outsider package) overridden then [m] else []
      | ClassDef _ _ _ _ _ _ | TypeDef _ _ _ => []
      | other => mentions other end) body.

  Definition entry_of (t : tree) : list entry :=
    match t with
    | DefDef (Member _ _ _ as s) _ _ _ rhs overridden =>
        [Entry s (match rhs with Some body => mentions body | None => [] end) overridden]
    | ValDef (Member _ _ _ as s) _ _ (Some rhs) => [Entry s (mentions rhs) []]
    | ClassDef _ _ (DefDef c _ _ _ _ _) parents _ body => [Entry c (constructs parents body) []]
    | _ => []
    end.

  Definition table : list entry := flat_map entry_of (over_list nodes files).

  Definition calls_of (s : sym) : list sym :=
    flat_map (fun e => if sym_eqb s (e_sym e) then e_calls e else []) table.
  Definition overriders (s : sym) : list sym :=
    flat_map (fun e => if known s (e_overrides e) then [e_sym e] else []) table.

  (** From `todo`, with `seen` reached already: what is reached, and what was left to look at when the fuel ran
      out (nothing, when there was enough). *)
  Fixpoint reach (fuel : nat) (todo seen : list sym) : list sym * list sym :=
    match fuel with
    | 0 => (seen, todo)
    | S fuel' =>
        match todo with
        | [] => (seen, [])
        | s :: rest =>
            if known s seen then reach fuel' rest seen
            else reach fuel' (filter (inside package) (calls_of s ++ overriders s) ++ rest) (s :: seen)
        end
    end.

  (** The definitions of the program declared by one of `owners`. *)
  Definition declared_by (owners : list string) : list sym :=
    filter (fun s => match s with Member o _ _ => existsb (String.eqb o) owners | _ => false end)
      (over_list defines files).

  (** What the definitions `from` reach, and what they take from outside the package. *)
  Definition reaches (from : list sym) : list sym * list sym :=
    reach (4 * length (over_list nodes files)) from [].
  Definition reaches_outside (reached : list sym) : list sym :=
    distinct (filter (outsider package) (flat_map calls_of reached)).

End Reach.
