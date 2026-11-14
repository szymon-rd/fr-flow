(** What a call of a method of a JDK class gives by its protocol (`Jdk.v`), each as an equation a proof rewrites
    with. A proof does not simplify the goal to find it: that would also compute what follows the call. *)

From Stdlib Require Import String List Bool.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine FrFlow.Scala.Tree FrFlow.Scala.Value FrFlow.Scala.Jdk.
Import ListNotations.
Open Scope string_scope.

Local Notation none := (@nil (Machine.val code obj)).
Local Notation one x := (@cons (Machine.val code obj) x (@nil (Machine.val code obj))).

(** ** AtomicBoolean *)
Lemma flag_get (t : tid) (intr v : bool) (choice : nat) :
  p_call atomic_boolean "get" t intr v none choice = Gives (inr (VBool v)) v.
Proof. reflexivity. Qed.

Lemma flag_set (t : tid) (intr v b : bool) (choice : nat) :
  p_call atomic_boolean "set" t intr v (one (VBool b)) choice = Gives (inr VUnit) b.
Proof. reflexivity. Qed.

(** ** ThreadLocal *)
Lemma local_get_call (t : tid) (intr : bool) (s : list (tid * val)) (choice : nat) :
  p_call thread_local "get" t intr s none choice = Gives (inr (of_thread s t)) s.
Proof. reflexivity. Qed.

Lemma local_set_call (t : tid) (intr : bool) (s : list (tid * val)) (v : val) (choice : nat) :
  p_call thread_local "set" t intr s (one v) choice = Gives (inr VUnit) ((t, v) :: s).
Proof. reflexivity. Qed.

(** ** AtomicReference *)
Lemma ref_get (t : tid) (intr : bool) (s : val) (choice : nat) :
  p_call atomic_reference "get" t intr s none choice = Gives (inr s) s.
Proof. reflexivity. Qed.

Lemma ref_getAndSet (t : tid) (intr : bool) (s v : val) (choice : nat) :
  p_call atomic_reference "getAndSet" t intr s (one v) choice = Gives (inr s) v.
Proof. reflexivity. Qed.
