(** What a method of Scala's collections gives where a proof needs it without the collection being known: of a
    collection of threads, asked whether it holds a thread. The library's functions over a collection are
    programs (two values are compared by `equal`, which may call a method of the program); over threads they
    call nothing, and are the function they look like. *)

From Stdlib Require Import String List Bool.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table
  FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Import ListNotations.

(** A list of threads, and whether it holds one. *)
Definition threads_only (xs : list val) : Prop := Forall (fun x => exists u : nat, x = VTid u) xs.

Definition has_thread (xs : list val) (u : nat) : bool :=
  existsb (fun y => match y with VTid a => same_place a u | _ => false end) xs.

Lemma threads_only_app (xs : list val) (u : nat) : threads_only xs -> threads_only (xs ++ [VTid u]).
Proof. intros H. apply Forall_app. split; [exact H |]. constructor; [exists u; reflexivity | constructor]. Qed.

(** Whether a collection of threads holds a thread: no program, a truth value. `same` is how two values are
    compared where the collection's method is called; of two threads it says whether they are the same. *)
Lemma any_thread (same : val -> X bool) (xs : list val) (u : nat) :
  threads_only xs -> (forall a : nat, same (VTid a) = oret (same_place a u)) ->
  any same xs = oret (has_thread xs u).
Proof.
  intros Hxs Hsame. induction Hxs as [| x rest [a ->] _ IH]; [reflexivity |].
  cbn [any has_thread existsb]. rewrite Hsame. cbn. rewrite IH. destruct (same_place a u); reflexivity.
Qed.
