(** What a Scala value is when the code runs, and what a piece of code gives.

    The meaning of Scala's trees (`Meaning.v`) is a program over the JVM's operations (`FrFlow.Jvm.Machine`).
    The machine leaves open what a closure and the program's data are; here they are said.

    - A value of the JVM's heap is a reference with its class (`Ref`): an object of the program, whose fields
      are in the machine's state, or an object of a class from outside, known by its protocol. A `var` is an
      object of the program with one field.
    - Scala's immutable data (an option, a tuple, a list, an `Either`) is the data itself (`Data`): two of them
      are told apart by what they hold, as their `equals` does, and nothing reads their identity.
    - A function is the tree of its definition with the variables in scope where it was made (`Fn`); an
      argument passed by name is its tree with those variables (`Thunk`). A method is named (`Method`): which
      body runs is found when it is called, from the class of what it is called on. *)

From Stdlib Require Import String List ZArith Bool DecimalString.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine FrFlow.Scala.Tree FrFlow.Scala.Equal.
Import ListNotations.
Open Scope string_scope.
Set Warnings "-register-all".

Inductive code :=
  (* a function made where it is written: its definition, the variables in scope, and the functions made in
     the same block, which it may call *)
  | Fn (def : tree) (scope : list (string * Machine.val code obj)) (group : list tree)
  (* an argument passed by name *)
  | Thunk (body : tree) (scope : list (string * Machine.val code obj))
  (* a method, called with what it is called on and its arguments *)
  | Method (s : sym)
  (* a method of one object: what a thread made from that object runs *)
  | Bound (s : sym) (on : Machine.val code obj)
  (* what making an object of a class runs: its parents' and its own initialisers *)
  | Init (cls : string)
with obj :=
  | Ref (cls : string) (r : nat)
  | Int (z : Z)
  | Long (z : Z)
  | Str (s : string)
  | Text                                           (* a text built from values: not known *)
  | Null
  | Data (constructor : string) (args : list (Machine.val code obj))
  | Module (name : string)                         (* an object that has no state of its own *)
  | ClassOf (name : string).

Definition val : Type := Machine.val code obj.
Definition scope : Type := list (string * val).

(** Whether two values are the same. *)
Fixpoint exn_eq_dec (a b : exn) : {a = b} + {a <> b}.
Proof. decide equality; auto using string_dec, Nat.eq_dec. Defined.

Section ValueEq.
  Variables (code obj : Type).
  Variable code_dec : forall a b : code, {a = b} + {a <> b}.
  Variable obj_dec : forall a b : obj, {a = b} + {a <> b}.

  Fixpoint value_eq_dec (a b : Machine.val code obj) {struct a} : {a = b} + {a <> b}.
  Proof. decide equality; auto using bool_dec, Nat.eq_dec, exn_eq_dec, list_eq_dec. Defined.
End ValueEq.

Fixpoint code_eq_dec (a b : code) {struct a} : {a = b} + {a <> b}
with obj_eq_dec (a b : obj) {struct a} : {a = b} + {a <> b}.
Proof.
  - decide equality; try (apply list_eq_dec; apply pair_eq_dec); try apply value_eq_dec;
      auto using string_dec, sym_eq_dec, tree_eq_dec, list_eq_dec.
  - decide equality; try (apply list_eq_dec; apply value_eq_dec);
      auto using string_dec, Nat.eq_dec, Z.eq_dec.
Defined.

Definition val_eq_dec : forall a b : val, {a = b} + {a <> b} := value_eq_dec code obj code_eq_dec obj_eq_dec.

Definition val_eqb (a b : val) : bool := if val_eq_dec a b then true else false.

Lemma val_eqb_eq a b : val_eqb a b = true <-> a = b.
Proof. unfold val_eqb. destruct (val_eq_dec a b); split; congruence. Qed.

Lemma val_eqb_refl a : val_eqb a a = true.
Proof. apply val_eqb_eq. reflexivity. Qed.

(** What running a piece of code gives: a value, or an exception thrown, or a `return` on its way out of the
    method `from`. *)
Inductive outcome (A : Type) : Type :=
  | Ok (a : A)
  | Exc (e : exn)
  | Brk (v : val) (from : string).
Arguments Ok {A} a.
Arguments Exc {A} e.
Arguments Brk {A} v from.

(** A program of the threads' language that gives an outcome. *)
Definition X (A : Type) : Type := Machine.P code obj (outcome A).

Definition oret {A : Type} (a : A) : X A := Ret (Ok a).
Definition othrow {A : Type} (e : exn) : X A := Ret (Exc e).
Definition obind {A B : Type} (m : X A) (f : A -> X B) : X B :=
  pbind m (fun o => match o with Ok a => f a | Exc e => Ret (Exc e) | Brk v from => Ret (Brk v from) end).

(** A call of an operation of the machine: one step. *)
Definition oop {Y : Type} (o : Machine.op code obj (exn + Y)) : X Y :=
  Vis o (fun r => match r with inl e => Ret (Exc e) | inr y => Ret (Ok y) end).

(** A call of a closure. *)
Definition ocall (c : code) (arg : val) : X val :=
  Call c arg (fun r => match r with inl e => Ret (Exc e) | inr v => Ret (Ok v) end).

(** Code this meaning does not cover: it may do anything (`Chaos`). A proof passes it only where it cannot be
    reached; a run stops at it. Nothing is given a meaning it does not have. *)
Definition stuck {A : Type} (why : string) : X A := Vis (Chaos (outcome A) why) (fun r => Ret r).

Declare Scope meaning_scope.
Notation "x <~ m ;; k" := (obind m (fun x => k))
  (at level 61, m at next level, right associativity) : meaning_scope.
Open Scope meaning_scope.

(** Each of a list, in order. *)
Fixpoint oeach {A B : Type} (f : A -> X B) (xs : list A) : X (list B) :=
  match xs with
  | [] => oret []
  | x :: rest => y <~ f x ;; ys <~ oeach f rest ;; oret (y :: ys)
  end.

(** ** Names

    A variable in scope is named by a text: a definition made inside a method by its name and its number, the
    object a method runs on by its class. *)

Definition nat_text (n : nat) : string := NilEmpty.string_of_uint (Nat.to_uint n).

Definition key (s : sym) : string :=
  match s with
  | Local name id => name ++ "#" ++ nat_text id
  | Member owner name _ => owner ++ "." ++ name
  | NoSym => ""
  end.

Definition this_key (cls : string) : string := "this:" ++ cls.

Fixpoint lookup (e : scope) (k : string) : option val :=
  match e with
  | [] => None
  | (k', v) :: rest => if String.eqb k' k then Some v else lookup rest k
  end.

(** ** The values the code writes *)

Definition vint (z : Z) : val := VObj (Int z).
Definition vlong (z : Z) : val := VObj (Long z).
Definition vstr (s : string) : val := VObj (Str s).
Definition vnull : val := VObj Null.
Definition vdata (c : string) (args : list val) : val := VObj (Data c args).
Definition vsome (v : val) : val := vdata "Some" [v].
Definition vnone : val := vdata "None" [].
Definition vref (cls : string) (r : nat) : val := VObj (Ref cls r).

(** Scala's `Int` and `Long` wrap around. *)
Definition wrap (bits : Z) (z : Z) : Z :=
  let m := Z.pow 2 bits in let r := Z.modulo z m in if Z.ltb r (Z.pow 2 (bits - 1)) then r else (r - m)%Z.
Definition int_of (z : Z) : val := vint (wrap 32 z).
Definition long_of (z : Z) : val := vlong (wrap 64 z).

Definition of_const (c : const) : option val :=
  match c with
  | CUnit => Some VUnit
  | CNull => Some vnull
  | CBool b => Some (VBool b)
  | CByte z | CShort z | CChar z | CInt z => Some (vint z)
  | CLong z => Some (vlong z)
  | CString s => Some (vstr s)
  | CClassOf name => Some (VObj (ClassOf name))
  | CFloat _ | CDouble _ => None
  end.

(** A variable is an object with one field. *)
Definition var_class : string := "<var>".
Definition var_field : string := "value".

(** A `lazy val` written in a method is an object that holds its value once it has one, and until then what
    gives it. *)
Definition lazy_class : string := "<lazy>".
Definition lazy_field : string := "value".
Definition thunk_field : string := "<thunk>".

(** The variables in scope where an object of a class written inside a method was made, kept in the object. *)
Definition scope_field : string := "<scope>".
Definition scope_val (e : scope) : val := VList (map (fun kv => vdata "" [vstr (fst kv); snd kv]) e).
Definition val_scope (v : val) : scope :=
  match v with
  | VList entries => flat_map (fun entry => match entry with
      | VObj (Data _ [VObj (Str k); x]) => [(k, x)]
      | _ => [] end) entries
  | _ => []
  end.
