(** What code calls that is outside it, in an execution (`Conforms.v`).

    What is computed stays computed: numbers, texts, data and collections that do not change mean what
    `Library.pure` says. A call of anything else (a method of the JDK, of a class the code was not read with) is
    one operation, named by the definition called: nothing is said here of what it gives. What it gives is what
    a model assumes of it, in the model's own words. *)

From Stdlib Require Import String List ZArith Bool.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Import ListNotations.
Open Scope string_scope.

(** A definition as an execution names it: its owner, its name and its signature. *)
Definition label (owner name signature : string) : string := owner ++ " " ++ name ++ " " ++ signature.

Definition label_of (s : sym) : string :=
  match s with Member owner name signature => label owner name signature | _ => "" end.

(** What a call is made on, where it is made on something: an object named alone (a package, an object with no
    state) is nothing a call is made on. *)
Definition receiver (v : val) : list val :=
  match v with VUnit | VObj (Module _) => [] | _ => [v] end.

(** A call of a definition from outside: one operation, of its label, on its receiver and its arguments. *)
Definition called (owner name signature : string) : primitive :=
  Prim [] (fun _ v _ args => oop (ExtCall 0 (label owner name signature) (receiver v ++ args))).

(** What is only named and never called: an object, a package. *)
Definition named_only (signature : string) : bool := String.eqb signature "" || String.eqb signature "package".

Definition outside (owner name signature : string) : option primitive :=
  match pure owner name with
  | Some p => Some p
  | None => if named_only signature then None else Some (called owner name signature)
  end.
