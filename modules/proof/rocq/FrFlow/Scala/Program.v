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

(** The members a tree defines: the values and methods a class or an object declares. *)
Fixpoint defines (t : tree) : list sym :=
  let many := fix go ts := match ts with [] => [] | x :: rest => defines x ++ go rest end in
  let maybe := fun o => match o with Some x => defines x | None => [] end in
  let own := fun s => match s with Member _ _ _ => [s] | _ => [] end in
  match t with
  | ValDef s _ _ rhs => own s ++ maybe rhs
  | DefDef s _ paramss _ rhs _ =>
      own s ++ (fix go pss := match pss with [] => [] | ps :: rest => many ps ++ go rest end) paramss ++ maybe rhs
  | ClassDef _ _ ctor parents self body => defines ctor ++ many parents ++ maybe self ++ many body
  | PackageClause _ stats => many stats
  | Block stats result => many stats ++ defines result
  | Apply f args => defines f ++ many args
  | TypeApply f _ => defines f
  | Select q _ => defines q
  | Typed e _ => defines e
  | NamedArg _ e => defines e
  | Assign l r => defines l ++ defines r
  | If c a b => defines c ++ defines a ++ defines b
  | Match _ s cases => defines s ++ many cases
  | SummonFrom cases => many cases
  | CaseDef _ g b => maybe g ++ defines b
  | Try b cases fin => defines b ++ many cases ++ maybe fin
  | Return e _ => defines e
  | While c b => defines c ++ defines b
  | Repeated es _ => many es
  | Inlined _ bs b => many bs ++ defines b
  | Closure m _ => defines m
  | _ => []
  end.

(** The definitions a tree refers to: every name it reads, selects or calls. *)
Fixpoint mentions (t : tree) : list sym :=
  let many := fix go ts := match ts with [] => [] | x :: rest => mentions x ++ go rest end in
  let maybe := fun o => match o with Some x => mentions x | None => [] end in
  match t with
  | Ident s => [s]
  | Select q s => s :: mentions q
  | SelectOuter q _ _ => mentions q
  | Super q _ => mentions q
  | Apply f args => mentions f ++ many args
  | TypeApply f _ => mentions f
  | NamedArg _ e => mentions e
  | Typed e _ => mentions e
  | Assign l r => mentions l ++ mentions r
  | Block stats result => many stats ++ mentions result
  | Closure m _ => mentions m
  | If c a b => mentions c ++ mentions a ++ mentions b
  | Match _ s cases => mentions s ++ many cases
  | SummonFrom cases => many cases
  | Try b cases fin => mentions b ++ many cases ++ maybe fin
  | Return e _ => mentions e
  | While c b => mentions c ++ mentions b
  | Repeated es _ => many es
  | Inlined call bs b => maybe call ++ many bs ++ mentions b
  | ValDef _ _ _ rhs => maybe rhs
  | DefDef _ _ paramss _ rhs _ =>
      (fix go pss := match pss with [] => [] | ps :: rest => many ps ++ go rest end) paramss ++ maybe rhs
  | ClassDef _ _ ctor parents self body => mentions ctor ++ many parents ++ maybe self ++ many body
  | PackageClause _ stats => many stats
  | CaseDef p g b => mentions p ++ maybe g ++ mentions b
  | Bind _ p => mentions p
  | Unapply f gs ps => mentions f ++ many gs ++ many ps
  | Alternatives ps => many ps
  | TypeTest p _ => mentions p
  | _ => []
  end.

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
