(** Whether two trees, two types or two values are the same: decided, so that a protocol that compares what it
    is given with what it holds (`compareAndSet`, a set's `contains`) is a function.

    Two values are the same when they are written the same: the JVM compares two references by which object
    each is, and so may tell apart two that are the same here. A protocol that compares says so where it
    matters. *)

From Stdlib Require Import String List ZArith Bool.
Require Import FrFlow.Scala.Tree.
Import ListNotations.

Definition option_eq_dec {A : Type} (dec : forall a b : A, {a = b} + {a <> b}) (x y : option A)
    : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition pair_eq_dec {A B : Type} (da : forall a b : A, {a = b} + {a <> b})
    (db : forall a b : B, {a = b} + {a <> b}) (x y : A * B) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition sym_eq_dec (a b : sym) : {a = b} + {a <> b}.
Proof. decide equality; auto using string_dec, Nat.eq_dec. Defined.

Definition const_eq_dec (a b : const) : {a = b} + {a <> b}.
Proof. decide equality; auto using string_dec, Z.eq_dec, bool_dec. Defined.

Fixpoint ty_eq_dec (a b : ty) {struct a} : {a = b} + {a <> b}.
Proof.
  decide equality; auto using string_dec, sym_eq_dec, const_eq_dec, list_eq_dec.
Defined.

Fixpoint tree_eq_dec (a b : tree) {struct a} : {a = b} + {a <> b}.
Proof.
  decide equality;
    auto using string_dec, sym_eq_dec, const_eq_dec, ty_eq_dec, Nat.eq_dec, bool_dec, list_eq_dec, option_eq_dec.
Defined.
