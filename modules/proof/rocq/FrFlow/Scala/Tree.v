(** Scala's typed trees, as the TASTy beside a class file holds them.

    A compiled Scala file is kept by the compiler as the tree it typed: every name resolved to the definition it
    means, every implicit argument and conversion written out, every type inferred. This is that tree as Rocq
    data, form for form: one constructor here for each form of tree and of type the compiler's reader gives
    (`scala.quoted.Quotes`). Code read into it is not interpreted in the reading: no form is chosen, dropped or
    rewritten, so the tree of a jar is the jar's code, whole.

    What is normalised, and nothing else:
    - a definition is named by where it is declared (`Member`: its owner, its name, its signature, which tells
      overloads apart) or, inside a method, by its name and a number (`Local`), since two locals may share a name;
    - a class declared inside a method is named with a number after `#`, for the same reason;
    - a type written in the source (a type tree) is the type it denotes;
    - a reference to a class or an alias reached by a fixed path is its full name (`TyRef`). *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
Set Warnings "-register-all".

(** A definition referred to. *)
Inductive sym :=
  | NoSym
  | Member (owner : string) (name : string) (signature : string)
  | Local (name : string) (id : nat).

Inductive const :=
  | CUnit
  | CNull
  | CBool (b : bool)
  | CByte (z : Z)
  | CShort (z : Z)
  | CChar (z : Z)
  | CInt (z : Z)
  | CLong (z : Z)
  | CFloat (text : string)
  | CDouble (text : string)
  | CString (s : string)
  | CClassOf (type : string).

Inductive ty :=
  | TyNone                                                  (* no prefix *)
  | TyRef (name : string)                                   (* a class or an alias, by its full name *)
  | TySelect (prefix : ty) (name : string)                  (* a type member of a path *)
  | TyParam (owner : string) (name : string)                (* a type parameter of a class or a method *)
  | TyTerm (s : sym)                                        (* the type of one value: `x.type` *)
  | TyThis (cls : string)
  | TySuper (this parent : ty)
  | TyApp (constructor : ty) (args : list ty)
  | TyConst (c : const)
  | TyByName (t : ty)
  | TyAnd (a b : ty)
  | TyOr (a b : ty)
  | TyAnnot (t : ty) (annotation : string)
  | TyRefine (parent : ty) (name : string) (info : ty)
  | TyBounds (lo hi : ty)
  | TyLambda (params : list string) (body : ty)
  | TyParamRef (name : string)                              (* a parameter of an enclosing lambda or method type *)
  | TyMethod (params : list string) (types : list ty) (result : ty)
  | TyPoly (params : list string) (result : ty)
  | TyMatch (bound scrutinee : ty) (cases : list ty)
  | TyCase (pattern result : ty)
  | TyRec (t : ty)
  | TyRecThis
  | TyFlexible (t : ty).

Inductive tree :=
  (* expressions *)
  | Ident (s : sym)
  | Select (qualifier : tree) (s : sym)
  | SelectOuter (qualifier : tree) (name : string) (levels : nat)
  | This (cls : string)
  | Super (qualifier : tree) (mix : option string)
  | Literal (c : const)
  | New (t : ty)
  | Apply (f : tree) (args : list tree)
  | TypeApply (f : tree) (targs : list ty)
  | NamedArg (name : string) (arg : tree)
  | Typed (e : tree) (t : ty)
  | Assign (lhs rhs : tree)
  | Block (stats : list tree) (result : tree)
  | Closure (method : tree) (t : option ty)
  | If (c thenp elsep : tree)
  | Match (inline : bool) (scrutinee : tree) (cases : list tree)
  | SummonFrom (cases : list tree)
  | Try (body : tree) (cases : list tree) (finalizer : option tree)
  | Return (e : tree) (from : sym)
  | While (c body : tree)
  | Repeated (elems : list tree) (t : ty)
  | Inlined (call : option tree) (bindings : list tree) (body : tree)
  (* definitions *)
  | ValDef (s : sym) (flags : list string) (t : ty) (rhs : option tree)
  | DefDef (s : sym) (flags : list string) (paramss : list (list tree)) (result : ty) (rhs : option tree)
      (overrides : list sym)
  | TypeDef (name : string) (flags : list string) (rhs : ty)
  | ClassDef (name : string) (flags : list string) (constructor : tree) (parents : list tree)
      (self : option tree) (body : list tree)
  | PackageClause (name : string) (stats : list tree)
  | Imported (from : tree) (selectors : list string)
  | Exported (from : tree) (selectors : list string)
  | TypeTree (t : ty)                                       (* a type where a tree stands: a parent of a class *)
  (* patterns *)
  | CaseDef (pattern : tree) (guard : option tree) (body : tree)
  | Bind (s : sym) (pattern : tree)
  | Unapply (f : tree) (implicits : list tree) (patterns : list tree)
  | Alternatives (patterns : list tree)
  | TypeTest (pattern : tree) (t : ty)
  | Wildcard
  (* a form the compiler's reader gives no access to: code of a macro, run by the compiler and not by the program *)
  | Other (kind : string) (shown : string).
