(** The effects of code read: what a tree of a program is over.

    A program names its classes, its fields, its methods and what it calls of code that is not read (`outside`)
    by types of its own, generated with it, each a finite list of names: a name that is not one is no term, and
    two names are told apart by computing. A field's type and a method's inputs and result are functions of the
    name, so an effect is typed by what it gives: reading a field of numbers gives a number.

    - `Get`, `Put`: a field of an object is read, written.
    - `New`: an object of a class is made, its fields holding what a field holds before it is written.
    - `Call`: a method of the code is called: it gives what the method's tree gives, or throws what it throws.
    - `Ext`: something outside the code is called. Nothing here says what it does. *)

From FrFlow.Effect Require Import Tree.

(** An object, by where it is; or none (`null`). *)
Inductive ref : Type :=
  | null
  | at_ (n : nat).

(** Whether two are the same object, or both none: Scala's `eq`. *)
Definition same (a b : ref) : bool :=
  match a, b with
  | null, null => true
  | at_ n, at_ m => Nat.eqb n m
  | _, _ => false
  end.

Section Sig.

  Variables class field method outside : Type.
  Variable field_ty : field -> Type.
  Variables (method_in method_out : method -> Type) (outside_in outside_out : outside -> Type).
  Variable exn : Type.

  Inductive eff : Type -> Type :=
    | Get (o : ref) (f : field) : eff (field_ty f)
    | Put (o : ref) (f : field) (v : field_ty f) : eff unit
    | New (c : class) : eff ref
    | Call (m : method) (given : method_in m) : eff (exn + method_out m)
    | Ext (m : outside) (given : outside_in m) : eff (exn + outside_out m).

  Definition get (o : ref) (f : field) : prog eff exn (field_ty f) := perform (Get o f).
  Definition put (o : ref) (f : field) (v : field_ty f) : prog eff exn unit := perform (Put o f v).
  Definition new (c : class) : prog eff exn ref := perform (New c).
  Definition call (m : method) (given : method_in m) : prog eff exn (method_out m) := attempt (Call m given).
  Definition ext (m : outside) (given : outside_in m) : prog eff exn (outside_out m) := attempt (Ext m given).

End Sig.

Arguments Get {class field method outside field_ty method_in method_out outside_in outside_out exn} o f.
Arguments Put {class field method outside field_ty method_in method_out outside_in outside_out exn} o f v.
Arguments New {class field method outside field_ty method_in method_out outside_in outside_out exn} c.
Arguments Call {class field method outside field_ty method_in method_out outside_in outside_out exn} m given.
Arguments Ext {class field method outside field_ty method_in method_out outside_in outside_out exn} m given.
