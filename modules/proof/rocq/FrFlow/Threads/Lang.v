(** What code read from Scala is written with: programs that may throw, and Scala's control as functions on
    them. Each definition here is the meaning given to one construct of the code read. *)

From Stdlib Require Import ZArith List Bool String.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem.
Import ListNotations.

Set Implicit Arguments.

Section Lang.

  Variables code obj : Type.
  Abbreviation val := (val code obj).
  Abbreviation op := (op code obj).

  (** A program that may throw. *)
  Definition M (A : Type) : Type := P code obj (exn + A).

  Definition ret {A : Type} (a : A) : M A := Ret (inr a).
  Definition throw {A : Type} (e : exn) : M A := Ret (inl e).

  Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B :=
    pbind m (fun r => match r with inl e => Ret (inl e) | inr a => f a end).

  (** A call of a method of the JDK. *)
  Definition call {X : Type} (o : op (exn + X)) : M X := Vis o (fun r => Ret r).

  (** A call of a closure: a by-name parameter read, a function value applied. *)
  Definition invoke (c : code) (arg : val) : M val := Call c arg (fun r => Ret r).

  (** `try m catch h`: `h` is given what was thrown; it rethrows what it does not handle. *)
  Definition try_catch {A : Type} (m : M A) (h : exn -> M A) : M A :=
    pbind m (fun r => match r with inl e => h e | inr a => Ret (inr a) end).

  (** `try m finally fin`: `fin` runs however `m` ends; what `fin` throws replaces what `m` gave. *)
  Definition try_finally {A : Type} (m : M A) (fin : M unit) : M A :=
    pbind m (fun r => pbind fin (fun r2 => match r2 with inl e => Ret (inl e) | inr _ => Ret r end)).

  (** A loop over a state: `body` gives the next state, or the result. `while` and a tail-recursive local
      function are both this. *)
  Definition loop {S B : Type} (body : S -> M (S + B)) (s : S) : M B :=
    Iter (fun s => pbind (body s) (fun r => match r with
      | inl e => Ret (inr (inl e))
      | inr (inl s') => Ret (inl s')
      | inr (inr b) => Ret (inr (inr b))
      end)) s (fun r => Ret r).

  (** `while cond do body`, over the variables the loop assigns. *)
  Definition while {S : Type} (cond : S -> M bool) (body : S -> M S) (s : S) : M S :=
    loop (fun s => bind (cond s) (fun c =>
      if c then bind (body s) (fun s' => ret (inl s')) else ret (inr s))) s.

  (** `set.forEach(f)` on a concurrent set of threads, over the variables `f` assigns: the traversal gives its
      elements one at a time, by the JDK's contract for it. *)
  Definition TsForEach {S : Type} (r : nat) (f : tid -> S -> M S) (s : S) : M S :=
    loop (fun st : list tid * S => let (seen, s) := st in
      bind (call (TsNext r seen)) (fun x => match x with
        | Some u => bind (f u s) (fun s' => ret (inl (u :: seen, s')))
        | None => ret (inr s)
        end)) ([], s).

  Definition EsForEach {S : Type} (r : nat) (f : exn -> S -> M S) (s : S) : M S :=
    loop (fun st : list exn * S => let (seen, s) := st in
      bind (call (EsNext r seen)) (fun x => match x with
        | Some e => bind (f e s) (fun s' => ret (inl (e :: seen, s')))
        | None => ret (inr s)
        end)) ([], s).

  Definition VsForEach {S : Type} (r : nat) (f : val -> S -> M S) (s : S) : M S :=
    loop (fun st : list val * S => let (seen, s) := st in
      bind (call (VsNext r seen)) (fun x => match x with
        | Some v => bind (f v s) (fun s' => ret (inl (v :: seen, s')))
        | None => ret (inr s)
        end)) ([], s).

  (** `list.foreach(f)`. *)
  Fixpoint List_foreach {A : Type} (xs : list A) (f : A -> M unit) : M unit :=
    match xs with
    | [] => ret tt
    | x :: xs' => bind (f x) (fun _ => List_foreach xs' f)
    end.

  Definition List_head {A : Type} (xs : list A) : M A :=
    match xs with x :: _ => ret x | [] => throw NoSuchElementException end.
  Definition List_tail {A : Type} (xs : list A) : M (list A) :=
    match xs with _ :: xs' => ret xs' | [] => throw (Other "java.lang.UnsupportedOperationException") end.
  Definition List_isEmpty {A : Type} (xs : list A) : bool :=
    match xs with [] => true | _ => false end.

  (** A reference that may be null, used where it must not be. *)
  Definition unnull {A : Type} (o : option A) : M A :=
    match o with Some a => ret a | None => throw NullPointerException end.

  (** A cast the compiler made. *)
  Definition type_error {A : Type} : M A := Vis (TypeError (exn + A)) (fun r => Ret r).

  (** Code that is not read. *)
  Definition chaos {A : Type} (what : string) : M A := Vis (Chaos (exn + A) what) (fun r => Ret r).

  (** A call of code that is not read and is taken to touch nothing of the JDK's state here. *)
  Definition extern {A : Type} (name : string) : M A := call (Extern A name).

  (** A set of threads held in a local variable (`Set[Thread]`). *)
  Definition tset_contains (s : list tid) (t : tid) : bool := existsb (Nat.eqb t) s.
  Definition tset_add (s : list tid) (t : tid) : list tid := t :: s.

  Fixpoint exn_eqb (a b : exn) : bool :=
    match a, b with
    | InterruptedException, InterruptedException => true
    | ExecutionException a', ExecutionException b' => exn_eqb a' b'
    | IllegalStateException, IllegalStateException => true
    | IllegalThreadStateException, IllegalThreadStateException => true
    | NullPointerException, NullPointerException => true
    | NoSuchElementException, NoSuchElementException => true
    | Other x, Other y => String.eqb x y
    | Thrown n, Thrown m => Nat.eqb n m
    | _, _ => false
    end.

End Lang.

Arguments ret {code obj A} a.
Arguments throw {code obj A} e.
Arguments bind {code obj A B} m f.
Arguments call {code obj X} o.
Arguments invoke {code obj} c arg.
Arguments try_catch {code obj A} m h.
Arguments try_finally {code obj A} m fin.
Arguments loop {code obj S B} body s.
Arguments while {code obj S} cond body s.
Arguments TsForEach {code obj S} r f s.
Arguments EsForEach {code obj S} r f s.
Arguments VsForEach {code obj S} r f s.
Arguments List_foreach {code obj A} xs f.
Arguments List_head {code obj A} xs.
Arguments List_tail {code obj A} xs.
Arguments unnull {code obj A} o.
Arguments type_error {code obj A}.
Arguments chaos {code obj A} what.
Arguments extern {code obj A} name.

Declare Scope prog_scope.
Notation "x <- m ;; k" := (bind m (fun x => k))
  (at level 61, m at next level, right associativity) : prog_scope.
Notation "' p <- m ;; k" := (bind m (fun p => k))
  (at level 61, p pattern, m at next level, right associativity) : prog_scope.
