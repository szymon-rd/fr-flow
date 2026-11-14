(** Where the meaning given to Ox's trees (`FrFlow.Scala.Meaning`, over `FrFlow.Scala.Library`) stops, as far as
    the trees themselves show it (`FrFlow.Scala.Gaps`), computed by Rocq from the trees.

    Of the kernel (`Kernel.v`: what the scopes, the forks and the operators built on them may run):

    - no tree is of a form the meaning stops at, no argument given by name is out of its place, and no class or
      object of it is declared inside a class (`kernel_whole`);
    - of the 184 definitions it takes from outside Ox, 13 have no meaning (`kernel_unmeant`): what the compiler
      makes for a case class and an object and no operator calls (a hash code, a serialization proxy), one
      extension method on Scala's futures (`Await.result`), and nine that are the compiler's own, used by the
      code of a macro when the compiler runs it and by no program.

    Of all of Ox: every argument given by name is in its place; six definitions hold a tree the meaning stops
    at (a choice the compiler makes where `either`'s four `ok` and its `fail` are inlined, and a floating-point
    constant);
    nine classes and objects are declared inside a class; and of the 513 definitions taken from outside, 183
    have no meaning (channels of jox, reactive streams, input and output, and the rest of Scala's library).
    A program that reaches one of those stops there (`Run.Stopped`), and says which.

    Kept by hand: when the trees or the library change, a lemma fails and the list is taken anew from what Rocq
    computes. *)

From Stdlib Require Import String List.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Scala.Library FrFlow.Scala.Gaps.
Require Import Ox.Tree.All Ox.Tree.Surface Ox.Tree.Kernel.
Import ListNotations.
Open Scope string_scope.

Definition T : table := Eval vm_compute in build files.
Definition everything : list sym := over_list defines files.

(** A class or an object of the kernel: one that declares a definition of it. *)
Definition of_kernel (cls : string) : bool :=
  existsb (fun s => match s with Member owner _ _ => String.eqb owner cls | _ => false end) kernel.

Lemma kernel_whole : (halts T kernel, misplaced T kernel, filter of_kernel (inner T)) = ([], [], []).
Proof. vm_compute. reflexivity. Qed.

Definition kernel_unmeant : list sym :=
  [Member "java.lang.String" "hashCode" ":scala.Int";
   Member "scala.concurrent.Await$" "result"
     "1,scala.concurrent.Awaitable,scala.concurrent.duration.Duration:java.lang.Object";
   Member "scala.quoted.Expr$" "apply" "1,java.lang.Object,scala.quoted.ToExpr,scala.quoted.Quotes:scala.quoted.Expr";
   Member "scala.quoted.Quotes.reflectModule" "TreeMethods" ":";
   Member "scala.quoted.Quotes.reflectModule" "asTerm" "scala.quoted.Expr:java.lang.Object";
   Member "scala.quoted.Quotes.reflectModule.PrinterModule" "TreeShortCode" ":";
   Member "scala.quoted.Quotes.reflectModule.TreeMethods" "show"
     "java.lang.Object,scala.quoted.Quotes.reflectModule.Printer:java.lang.String";
   Member "scala.quoted.ToExpr$" "StringToExpr" "1:scala.quoted.ToExpr$.StringToExpr";
   Member "scala.quoted.Type$" "of" "1,scala.quoted.Quotes:scala.quoted.Type";
   Member "scala.quoted.runtime.Expr$" "quote" "1,java.lang.Object:scala.Function1";
   Member "scala.quoted.runtime.Expr$" "splice" "1,scala.Function1:java.lang.Object";
   Member "scala.runtime.ModuleSerializationProxy" "<init>"
     "java.lang.Class:scala.runtime.ModuleSerializationProxy";
   Member "scala.util.hashing.MurmurHash3" "productHash" "scala.Product,scala.Int,scala.Boolean:scala.Int"].

Lemma kernel_unmeant_is : unmeant T outside kernel_surface = kernel_unmeant.
Proof. vm_compute. reflexivity. Qed.

(** All of Ox. *)
Definition halting : list (string * string) :=
  [("ox.either$", "ok"); ("ox.either$", "ok"); ("ox.either$", "ok"); ("ox.either$", "ok"); ("ox.either$", "fail");
   ("ox.flow.FlowCompanionReactiveOps", "fromPublisher")].

Lemma halting_is :
  map (fun s => match s with Member owner name _ => (owner, name) | _ => ("", "") end)
    (distinct (map fst (halts T everything))) = halting.
Proof. vm_compute. reflexivity. Qed.

Lemma named_in_place : misplaced T everything = [].
Proof. vm_compute. reflexivity. Qed.

Lemma inner_is : inner T =
  ["ox.channels.Sink.Sent"; "ox.channels.Sink.Sent$"; "ox.channels.Sink.Send"; "ox.channels.Sink.Send$";
   "ox.channels.Source.Received"; "ox.channels.Source.Received$"; "ox.channels.Source.Receive";
   "ox.channels.Source.Receive$"; "ox.flow.FlowOps.NotSent$"].
Proof. vm_compute. reflexivity. Qed.

Lemma outside_unmeant : (length surface, length (unmeant T outside surface)) = (513, 183).
Proof. vm_compute. reflexivity. Qed.
