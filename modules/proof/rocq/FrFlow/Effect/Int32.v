(** Scala's `Int`, as the JVM computes it: a whole number of 32 bits, an operation's result wrapped into them. *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Definition wrap (z : Z) : Z := (z + 2147483648) mod 4294967296 - 2147483648.

Definition iadd (a b : Z) : Z := wrap (a + b).
Definition isub (a b : Z) : Z := wrap (a - b).
Definition imul (a b : Z) : Z := wrap (a * b).
Definition ineg (a : Z) : Z := wrap (- a).

Lemma wrap_small (z : Z) : -2147483648 <= z < 2147483648 -> wrap z = z.
Proof. intros H. unfold wrap. rewrite Z.mod_small; lia. Qed.
