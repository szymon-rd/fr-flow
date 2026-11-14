(** What is assumed of the JDK's classes: for each, the state of an object of it and what each of its methods
    does (`Machine.protocol`).

    Each method is one step among the steps of other threads: that is what the classes' documentation says of
    them (each is "atomic", or "thread-safe" with every method taking effect at one moment). A method that waits
    does not return until it can; one that the documentation says throws `InterruptedException` does so when
    the caller is interrupted, as each says: on entry (`Semaphore.acquire`, a queue's `put` and `take`) or only
    while it waits (`CompletableFuture.get`).

    Where a class may do one of several things the protocol takes a number (`choice`): which element a
    traversal gives next, whether a `compareAndSet` whose expected value is the one held succeeds. The second
    is so because the JVM compares references and two values the same here may be two objects there: it may
    fail where this would succeed, so the failure is allowed.

    One row says more than the JDK promises. `isEmpty` of a concurrent set answers here whether the set is
    empty; `ConcurrentHashMap` documents it as "typically useful only when a map is not undergoing concurrent
    updates", and on JDK 21 it has answered `true` of a set that was never empty
    (`examples/ox/probe/IsEmptyProbe.scala`). What is proven of Ox's scopes rests on this row. *)

From Stdlib Require Import String List ZArith Bool.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine FrFlow.Scala.Tree FrFlow.Scala.Value.
Import ListNotations.
Open Scope string_scope.

Definition protocol : Type := Machine.protocol code obj.
Definition answer (S : Type) : Type := reply code obj S.

(** A value thrown: an exception of the JDK, or an object of a class of the program. *)
Definition as_exn (v : val) : option exn :=
  match v with
  | VExn x => Some x
  | VObj (Ref _ r) => Some (Thrown r)
  | _ => None
  end.

Definition named (method name : string) : bool := String.eqb method name.
Definition unit_ {S : Type} (s : S) : answer S := Gives (inr VUnit) s.
Definition truth_ {S : Type} (b : bool) (s : S) : answer S := Gives (inr (VBool b)) s.
Definition holds (xs : list val) (x : val) : bool := existsb (val_eqb x) xs.
Definition without (xs : list val) (x : val) : list val := filter (fun y => negb (val_eqb x y)) xs.

(** ** java.util.concurrent.atomic.AtomicBoolean: its value *)

Definition atomic_boolean : protocol := {|
  p_class := "java.util.concurrent.atomic.AtomicBoolean";
  p_methods := ["get"; "set"; "getAndSet"; "compareAndSet"];
  p_state := bool;
  p_new := fun args => match args with [] => Some false | [VBool b] => Some b | _ => None end;
  p_call := fun method _ _ s args _ =>
    match args with
    | [] => if named method "get" then truth_ s s else Unknown
    | [VBool b] =>
        if named method "set" then unit_ b
        else if named method "getAndSet" then truth_ s b
        else Unknown
    | [VBool expected; VBool b] =>
        if named method "compareAndSet" then (if Bool.eqb s expected then truth_ true b else truth_ false s)
        else Unknown
    | _ => Unknown
    end |}.

(** ** java.util.concurrent.atomic.AtomicInteger: its value, which wraps as an `int` does *)

Definition atomic_integer : protocol := {|
  p_class := "java.util.concurrent.atomic.AtomicInteger";
  p_methods := ["get"; "set"; "incrementAndGet"; "decrementAndGet"; "getAndIncrement"; "getAndDecrement";
                "addAndGet"; "compareAndSet"];
  p_state := Z;
  p_new := fun args => match args with [] => Some 0%Z | [VObj (Int z)] => Some z | _ => None end;
  p_call := fun method _ _ s args _ =>
    let next (d : Z) : Z := wrap 32 (s + d) in
    match args with
    | [] =>
        if named method "get" then Gives (inr (vint s)) s
        else if named method "incrementAndGet" then Gives (inr (vint (next 1%Z))) (next 1%Z)
        else if named method "decrementAndGet" then Gives (inr (vint (next (-1)%Z))) (next (-1)%Z)
        else if named method "getAndIncrement" then Gives (inr (vint s)) (next 1%Z)
        else if named method "getAndDecrement" then Gives (inr (vint s)) (next (-1)%Z)
        else Unknown
    | [VObj (Int z)] =>
        if named method "set" then unit_ z
        else if named method "addAndGet" then Gives (inr (vint (next z))) (next z)
        else Unknown
    | [VObj (Int expected); VObj (Int z)] =>
        if named method "compareAndSet" then (if Z.eqb s expected then truth_ true z else truth_ false s)
        else Unknown
    | _ => Unknown
    end |}.

(** ** java.util.concurrent.atomic.AtomicReference: what it refers to

    `updateAndGet` is not here: it calls a function of the program, and is the loop the class documents (read,
    apply, `compareAndSet`, again if that failed), in `Library.v`. *)

Definition atomic_reference : protocol := {|
  p_class := "java.util.concurrent.atomic.AtomicReference";
  p_methods := ["get"; "set"; "getAndSet"; "compareAndSet"];
  p_state := val;
  p_new := fun args => match args with [] => Some vnull | [v] => Some v | _ => None end;
  p_call := fun method _ _ s args choice =>
    match args with
    | [] => if named method "get" then Gives (inr s) s else Unknown
    | [v] =>
        if named method "set" then unit_ v
        else if named method "getAndSet" then Gives (inr s) v
        else Unknown
    | [expected; v] =>
        if named method "compareAndSet"
        then (if val_eqb s expected && Nat.eqb choice 0 then truth_ true v else truth_ false s)
        else Unknown
    | _ => Unknown
    end |}.

(** ** java.util.concurrent.CompletableFuture: not completed, or how

    Completed at most once; `complete` and `completeExceptionally` say whether theirs was the completion; `get`
    returns once it is completed, with the value, or throws `ExecutionException` over the cause. *)

Definition completable_future : protocol := {|
  p_class := "java.util.concurrent.CompletableFuture";
  p_methods := ["complete"; "completeExceptionally"; "get"; "isDone"; "isCompletedExceptionally";
                "exceptionNow"];
  p_state := option (exn + val);
  p_new := fun args => match args with [] => Some None | _ => None end;
  p_call := fun method _ _ s args _ =>
    match args with
    | [] =>
        if named method "get" then
          match s with
          | None => Waits
          | Some (inr v) => Gives (inr v) s
          | Some (inl e) => Gives (inl (ExecutionException e)) s
          end
        else if named method "isDone" then truth_ (match s with Some _ => true | None => false end) s
        else if named method "isCompletedExceptionally" then
          truth_ (match s with Some (inl _) => true | _ => false end) s
        else if named method "exceptionNow" then
          match s with
          | Some (inl e) => Gives (inr (VExn e)) s
          | _ => Gives (inl IllegalStateException) s
          end
        else Unknown
    | [v] =>
        if named method "complete" then
          match s with None => truth_ true (Some (inr v)) | Some _ => truth_ false s end
        else if named method "completeExceptionally" then
          match as_exn v, s with
          | Some e, None => truth_ true (Some (inl e))
          | Some _, Some _ => truth_ false s
          | None, _ => Unknown
          end
        else Unknown
    | _ => Unknown
    end |}.

(** ** java.lang.ThreadLocal: what each thread set; a thread reads what it set, or no object *)

Fixpoint of_thread (held : list (tid * val)) (t : tid) : val :=
  match held with
  | [] => vnull
  | (u, v) :: rest => if Nat.eqb u t then v else of_thread rest t
  end.

Definition thread_local : protocol := {|
  p_class := "java.lang.ThreadLocal";
  p_methods := ["get"; "set"; "remove"];
  p_state := list (tid * val);
  p_new := fun args => match args with [] => Some [] | _ => None end;
  p_call := fun method t _ s args _ =>
    match args with
    | [] =>
        if named method "get" then Gives (inr (of_thread s t)) s
        else if named method "remove" then unit_ ((t, vnull) :: s)
        else Unknown
    | [v] => if named method "set" then unit_ ((t, v) :: s) else Unknown
    | _ => Unknown
    end |}.

(** ** A concurrent set (`ConcurrentHashMap.newKeySet`): its elements

    `next` is one step of a traversal (`forEach`, an iterator): given the elements the traversal has passed, one
    that is in the set and not among them, or none when there is none. A traversal is "weakly consistent": it
    passes what is in the set as it goes, and may or may not pass what is added meanwhile. *)

Definition concurrent_set : protocol := {|
  p_class := "java.util.concurrent.ConcurrentHashMap$.KeySetView";
  p_methods := ["add"; "remove"; "contains"; "isEmpty"; "next"];
  p_state := list val;
  p_new := fun args => match args with [] => Some [] | _ => None end;
  p_call := fun method _ _ s args choice =>
    match args with
    | [] => if named method "isEmpty" then truth_ (match s with [] => true | _ => false end) s else Unknown
    | [x] =>
        if named method "add" then (if holds s x then truth_ false s else truth_ true (s ++ [x])%list)
        else if named method "remove" then truth_ (holds s x) (without s x)
        else if named method "contains" then truth_ (holds s x) s
        else if named method "next" then
          match x with
          | VList passed =>
              let left := filter (fun y => negb (holds passed y)) s in
              Gives (inr (match nth_error left (Nat.modulo choice (Nat.max 1 (List.length left))) with
                          | Some y => vsome y
                          | None => vnone
                          end)) s
          | _ => Unknown
          end
        else Unknown
    | _ => Unknown
    end |}.

(** ** java.util.concurrent.Semaphore: its permits *)

Definition semaphore : protocol := {|
  p_class := "java.util.concurrent.Semaphore";
  p_methods := ["acquire"; "release"];
  p_state := Z;
  p_new := fun args => match args with [VObj (Int n)] | [VObj (Int n); VBool _] => Some n | _ => None end;
  p_call := fun method _ interrupted s args _ =>
    match args with
    | [] =>
        if named method "acquire" then
          (if interrupted then Interrupted else if (0 <? s)%Z then unit_ (s - 1)%Z else Waits)
        else if named method "release" then unit_ (s + 1)%Z
        else Unknown
    | _ => Unknown
    end |}.

(** ** java.util.concurrent.ArrayBlockingQueue: its capacity and its elements, first in first out *)

Definition array_blocking_queue : protocol := {|
  p_class := "java.util.concurrent.ArrayBlockingQueue";
  p_methods := ["put"; "take"];
  p_state := nat * list val;
  p_new := fun args => match args with [VObj (Int n)] => Some (Z.to_nat n, []) | _ => None end;
  p_call := fun method _ interrupted s args _ =>
    match args with
    | [] =>
        if named method "take" then
          (if interrupted then Interrupted else
           match snd s with x :: rest => Gives (inr x) (fst s, rest) | [] => Waits end)
        else Unknown
    | [v] =>
        if named method "put" then
          (if interrupted then Interrupted else
           if Nat.ltb (List.length (snd s)) (fst s) then unit_ (fst s, (snd s ++ [v])%list) else Waits)
        else Unknown
    | _ => Unknown
    end |}.

(** ** The classes, and what else names each

    A method of a class is also called by the name of what the class inherits it from (`java.util.Set.add` on a
    concurrent set). *)

Definition classes : list (protocol * list string) :=
  [(atomic_boolean, []); (atomic_integer, []); (atomic_reference, []); (completable_future, []);
   (thread_local, []);
   (concurrent_set, ["java.util.Set"; "java.util.Collection"; "java.lang.Iterable";
                     "java.util.concurrent.ConcurrentHashMap$.CollectionView"]);
   (semaphore, []); (array_blocking_queue, [])].

(** The protocol of the class `owner` names, if it has the method. *)
Definition class_with (owner method : string) : option protocol :=
  match find (fun entry => (String.eqb (p_class (fst entry)) owner || existsb (String.eqb owner) (snd entry))
                           && existsb (String.eqb method) (p_methods (fst entry))) classes with
  | Some entry => Some (fst entry)
  | None => None
  end.

Definition class_named (owner : string) : option protocol :=
  match find (fun entry => String.eqb (p_class (fst entry)) owner) classes with
  | Some entry => Some (fst entry)
  | None => None
  end.
