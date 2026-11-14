(** What a program takes from outside itself: the JDK's classes and Scala's library, as the meaning of a call of
    each (`Meaning.primitive`).

    - A member of the JDK is the operation of its contract (`FrFlow.Threads.Jdk`): one step among the steps of
      other threads, and nothing else is assumed of it. An object of the JDK is a reference with its class.
    - Scala's data (an option, a tuple, a list, an `Either`, a vector, a set, a map) is data, and a method of
      it is the function it is. A method that takes a function calls it.
    - A text built from values is not known (`Text`); a number wraps as the JVM's does.

    A definition that is not here has no meaning: a call of it is `stuck`. *)

From Stdlib Require Import String List ZArith Bool.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Scala.Jdk.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope meaning_scope.

Definition Eq : Type := val -> val -> X bool.
Definition Run : Type := context -> val -> list ty -> list val -> X val.

Definition wrong {A : Type} (what : string) : X A := stuck (cat "a call from outside not as its meaning takes it: " what).

(** ** Classes of the data *)

Definition c_some := "scala.Some".
Definition c_none := "scala.None$".
Definition c_left := "scala.util.Left".
Definition c_right := "scala.util.Right".
Definition c_vector := "scala.collection.immutable.Vector".
Definition c_set := "scala.collection.immutable.Set".
Definition c_map := "scala.collection.immutable.Map".
Definition c_success := "scala.util.Success".
Definition c_failure := "scala.util.Failure".
Definition c_duration := "scala.concurrent.duration.FiniteDuration".
Definition c_forever := "scala.concurrent.duration.Duration$.Infinite".
Definition tuple (n : nat) : string := cat "scala.Tuple" (nat_text n).

Definition some (v : val) : val := vdata c_some [v].
Definition none : val := vdata c_none [].
Definition pair (a b : val) : val := vdata (tuple 2) [a; b].

(** What a class from outside inherits from, as far as the code tests it. *)
Definition supers (cls : string) : list string :=
  let throwable := ["java.lang.Throwable"] in
  let exception := "java.lang.Exception" :: throwable in
  let runtime := "java.lang.RuntimeException" :: exception in
  if String.eqb cls "java.lang.InterruptedException" then exception
  else if String.eqb cls "java.util.concurrent.ExecutionException" then exception
  else if String.eqb cls "java.util.concurrent.TimeoutException" then exception
  else if String.eqb cls "java.lang.Exception" then throwable
  else if String.eqb cls "java.lang.RuntimeException" then exception
  else if String.eqb cls "java.lang.IllegalStateException" then runtime
  else if String.eqb cls "java.lang.IllegalArgumentException" then runtime
  else if String.eqb cls "java.lang.IllegalThreadStateException" then "java.lang.IllegalArgumentException" :: runtime
  else if String.eqb cls "java.lang.NullPointerException" then runtime
  else if String.eqb cls "java.lang.ClassCastException" then runtime
  else if String.eqb cls "java.lang.IndexOutOfBoundsException" then runtime
  else if String.eqb cls "java.lang.ArrayIndexOutOfBoundsException" then
    "java.lang.IndexOutOfBoundsException" :: runtime
  else if String.eqb cls "java.lang.ArithmeticException" then runtime
  else if String.eqb cls "java.lang.UnsupportedOperationException" then runtime
  else if String.eqb cls "java.util.NoSuchElementException" then runtime
  else if String.eqb cls "scala.MatchError" then runtime
  else if String.eqb cls "java.lang.Error" then throwable
  else if String.eqb cls c_some || String.eqb cls c_none then ["scala.Option"; "scala.Product"]
  else if String.eqb cls c_left || String.eqb cls c_right then ["scala.util.Either"; "scala.Product"]
  else if String.eqb cls c_success || String.eqb cls c_failure then ["scala.util.Try"; "scala.Product"]
  else if String.eqb cls "scala.collection.immutable.::" || String.eqb cls "scala.collection.immutable.Nil$" then
    ["scala.collection.immutable.List"; "scala.collection.immutable.Seq"; "scala.collection.Seq";
     "scala.collection.Iterable"; "scala.collection.IterableOnce"]
  else if String.eqb cls c_vector then
    ["scala.collection.immutable.Seq"; "scala.collection.Seq"; "scala.collection.Iterable";
     "scala.collection.IterableOnce"]
  else if String.eqb cls c_duration || String.eqb cls c_forever then ["scala.concurrent.duration.Duration"]
  else [].

(** ** Values read as what an operation takes *)

Definition nullable (v : val) : option val := match v with VObj Null => None | _ => Some v end.
Definition of_nullable (o : option val) : val := match o with Some v => v | None => vnull end.

(** An exception of a class of the JDK, made. *)
Definition made_exn (cls : string) : exn :=
  if String.eqb cls "java.lang.InterruptedException" then InterruptedException
  else if String.eqb cls "java.lang.IllegalStateException" then IllegalStateException
  else if String.eqb cls "java.lang.IllegalThreadStateException" then IllegalThreadStateException
  else if String.eqb cls "java.lang.NullPointerException" then NullPointerException
  else if String.eqb cls "java.util.NoSuchElementException" then NoSuchElementException
  else Machine.Other cls.

(** A function value called. *)
Definition apply_fn (f : val) (args : list val) : X val :=
  match f with
  | VCode c => ocall c (VList args)
  | _ => wrong "what is applied is no function"
  end.

(** ** Collections

    A list is its elements; a vector, a set and a map are data over a list of theirs. *)

Definition elems (v : val) : option (list val) :=
  match v with
  | VList xs => Some xs
  | VObj (Data _ [VList xs]) => Some xs
  | _ => None
  end.

(** The same kind of collection as `like`, with other elements. *)
Definition rebuilt (like : val) (xs : list val) : val :=
  match like with
  | VObj (Data c [VList _]) => vdata c [VList xs]
  | _ => VList xs
  end.

Fixpoint each (f : val -> X val) (xs : list val) : X (list val) :=
  match xs with
  | [] => oret []
  | x :: rest => y <~ f x ;; ys <~ each f rest ;; oret (y :: ys)
  end.

Fixpoint any (p : val -> X bool) (xs : list val) : X bool :=
  match xs with
  | [] => oret false
  | x :: rest => b <~ p x ;; if b then oret true else any p rest
  end.

Fixpoint keep (p : val -> X bool) (xs : list val) : X (list val) :=
  match xs with
  | [] => oret []
  | x :: rest => b <~ p x ;; ys <~ keep p rest ;; oret (if b then x :: ys else ys)
  end.

Fixpoint fold (f : val -> val -> X val) (acc : val) (xs : list val) : X val :=
  match xs with
  | [] => oret acc
  | x :: rest => acc' <~ f acc x ;; fold f acc' rest
  end.

Definition truth (v : val) : X bool :=
  match v with VBool b => oret b | _ => wrong "a function that gave no truth value" end.

(** A method of a collection, by its name: the same for a list, a vector, a set, whatever declares it. *)
Definition collection (name : string) : option Run :=
  let on (f : Eq -> val -> list val -> list val -> X val) : option Run :=
    Some (fun ctx v _ args => match elems v with Some xs => f (c_eq ctx) v xs args | None => wrong name end) in
  let called (n : string) := String.eqb name n in
  if called "foreach" then on (fun _ _ xs args => match args with
    | [f] => _ <~ each (fun x => apply_fn f [x]) xs ;; oret VUnit
    | _ => wrong name end)
  else if called "map" then on (fun _ v xs args => match args with
    | [f] => ys <~ each (fun x => apply_fn f [x]) xs ;; oret (rebuilt v ys)
    | _ => wrong name end)
  else if called "flatMap" then on (fun _ v xs args => match args with
    | [f] =>
        ys <~ each (fun x => apply_fn f [x]) xs ;;
        oret (rebuilt v (flat_map (fun y => match elems y with Some zs => zs | None => [] end) ys))
    | _ => wrong name end)
  else if called "exists" then on (fun _ _ xs args => match args with
    | [f] => b <~ any (fun x => r <~ apply_fn f [x] ;; truth r) xs ;; oret (VBool b)
    | _ => wrong name end)
  else if called "forall" then on (fun _ _ xs args => match args with
    | [f] => b <~ any (fun x => r <~ apply_fn f [x] ;; t <~ truth r ;; oret (negb t)) xs ;; oret (VBool (negb b))
    | _ => wrong name end)
  else if called "filter" then on (fun _ v xs args => match args with
    | [f] => ys <~ keep (fun x => r <~ apply_fn f [x] ;; truth r) xs ;; oret (rebuilt v ys)
    | _ => wrong name end)
  else if called "foldLeft" then on (fun _ _ xs args => match args with
    | [z; f] => fold (fun acc x => apply_fn f [acc; x]) z xs
    | _ => wrong name end)
  else if called "isEmpty" then on (fun _ _ xs _ => oret (VBool (match xs with [] => true | _ => false end)))
  else if called "nonEmpty" then on (fun _ _ xs _ => oret (VBool (match xs with [] => false | _ => true end)))
  else if called "size" || called "length" then on (fun _ _ xs _ => oret (vint (Z.of_nat (List.length xs))))
  else if called "head" then on (fun _ _ xs _ => match xs with
    | x :: _ => oret x
    | [] => othrow NoSuchElementException end)
  else if called "headOption" then on (fun _ _ xs _ => oret (match xs with x :: _ => some x | [] => none end))
  else if called "tail" then on (fun _ v xs _ => match xs with
    | _ :: rest => oret (rebuilt v rest)
    | [] => othrow (Machine.Other "java.lang.UnsupportedOperationException") end)
  else if called "reverse" then on (fun _ v xs _ => oret (rebuilt v (rev xs)))
  else if called "toList" then on (fun _ _ xs _ => oret (VList xs))
  else if called "toVector" then on (fun _ _ xs _ => oret (vdata c_vector [VList xs]))
  else if called "toSeq" then on (fun _ v _ _ => oret v)
  else if called "::" then on (fun _ _ xs args => match args with [x] => oret (VList (x :: xs)) | _ => wrong name end)
  else if called ":+" || called "appended" then on (fun _ v xs args => match args with
    | [x] => oret (rebuilt v (xs ++ [x]))
    | _ => wrong name end)
  else if called "+:" || called "prepended" then on (fun _ v xs args => match args with
    | [x] => oret (rebuilt v (x :: xs))
    | _ => wrong name end)
  else if called "++" || called "concat" || called ":::" then on (fun _ v xs args => match args with
    | [w] => match elems w with Some ys => oret (rebuilt v (xs ++ ys)) | None => wrong name end
    | _ => wrong name end)
  else if called "apply" then on (fun _ _ xs args => match args with
    | [VObj (Int i)] => match nth_error xs (Z.to_nat i) with
        | Some x => oret x
        | None => othrow (Machine.Other "java.lang.IndexOutOfBoundsException") end
    | _ => wrong name end)
  else if called "contains" then on (fun eq _ xs args => match args with
    | [x] => b <~ any (fun y => eq y x) xs ;; oret (VBool b)
    | _ => wrong name end)
  else if called "+" || called "incl" then on (fun eq v xs args => match args with
    | [x] => b <~ any (fun y => eq y x) xs ;; oret (if b then v else rebuilt v (xs ++ [x]))
    | _ => wrong name end)
  else if called "-" || called "excl" then on (fun eq v xs args => match args with
    | [x] => ys <~ keep (fun y => b <~ eq y x ;; oret (negb b)) xs ;; oret (rebuilt v ys)
    | _ => wrong name end)
  else None.

(** A map: its entries, each a pair. *)
Definition entry_key (e : val) : val := match e with VObj (Data _ [k; _]) => k | _ => VUnit end.
Definition entry_value (e : val) : val := match e with VObj (Data _ [_; v]) => v | _ => VUnit end.

Fixpoint find_entry (eq : Eq) (k : val) (es : list val) : X (option val) :=
  match es with
  | [] => oret None
  | e :: rest => b <~ eq (entry_key e) k ;; if b then oret (Some (entry_value e)) else find_entry eq k rest
  end.

Definition map_method (name : string) : option Run :=
  let on (f : Eq -> list val -> list val -> X val) : option Run :=
    Some (fun ctx v _ args => match v with
      | VObj (Data _ [VList es]) => f (c_eq ctx) es args
      | _ => wrong name end) in
  let called (n : string) := String.eqb name n in
  let without (eq : Eq) (k : val) (es : list val) : X (list val) :=
    keep (fun e => b <~ eq (entry_key e) k ;; oret (negb b)) es in
  if called "get" then on (fun eq es args => match args with
    | [k] => r <~ find_entry eq k es ;; oret (match r with Some v => some v | None => none end)
    | _ => wrong name end)
  else if called "contains" then on (fun eq es args => match args with
    | [k] => r <~ find_entry eq k es ;; oret (VBool (match r with Some _ => true | None => false end))
    | _ => wrong name end)
  else if called "apply" then on (fun eq es args => match args with
    | [k] => r <~ find_entry eq k es ;;
        match r with Some v => oret v | None => othrow NoSuchElementException end
    | _ => wrong name end)
  else if called "getOrElse" then on (fun eq es args => match args with
    | [k; d] => r <~ find_entry eq k es ;; match r with Some v => oret v | None => apply_fn d [] end
    | _ => wrong name end)
  else if called "updated" then on (fun eq es args => match args with
    | [k; v] => rest <~ without eq k es ;; oret (vdata c_map [VList (rest ++ [pair k v])])
    | _ => wrong name end)
  else if called "+" then on (fun eq es args => match args with
    | [VObj (Data _ [k; v])] => rest <~ without eq k es ;; oret (vdata c_map [VList (rest ++ [pair k v])])
    | _ => wrong name end)
  else if called "removed" || called "-" then on (fun eq es args => match args with
    | [k] => rest <~ without eq k es ;; oret (vdata c_map [VList rest])
    | _ => wrong name end)
  else None.

Definition is_map (v : val) : bool :=
  match v with VObj (Data c _) => String.eqb c c_map | _ => false end.

(** A method of an option. *)
Definition option_method (name : string) : option (list bool * Run) :=
  let called (n : string) := String.eqb name n in
  let on (lazy : list bool) (f : option val -> list val -> X val) : option (list bool * Run) :=
    Some (lazy, fun _ v _ args => match v with
      | VObj (Data c xs) =>
          if String.eqb c c_none then f None args
          else match xs with [x] => f (Some x) args | _ => wrong name end
      | _ => wrong name end) in
  if called "getOrElse" then on [true] (fun o args => match o, args with
    | Some x, _ => oret x
    | None, [d] => apply_fn d []
    | _, _ => wrong name end)
  else if called "orElse" then on [true] (fun o args => match o, args with
    | Some x, _ => oret (some x)
    | None, [d] => apply_fn d []
    | _, _ => wrong name end)
  else if called "isDefined" || called "nonEmpty" then on [] (fun o _ => oret (VBool (match o with Some _ => true | None => false end)))
  else if called "isEmpty" then on [] (fun o _ => oret (VBool (match o with Some _ => false | None => true end)))
  else if called "get" then on [] (fun o _ => match o with Some x => oret x | None => othrow NoSuchElementException end)
  else if called "map" then on [] (fun o args => match o, args with
    | Some x, [f] => y <~ apply_fn f [x] ;; oret (some y)
    | None, [_] => oret none
    | _, _ => wrong name end)
  else if called "flatMap" then on [] (fun o args => match o, args with
    | Some x, [f] => apply_fn f [x]
    | None, [_] => oret none
    | _, _ => wrong name end)
  else if called "foreach" then on [] (fun o args => match o, args with
    | Some x, [f] => _ <~ apply_fn f [x] ;; oret VUnit
    | None, [_] => oret VUnit
    | _, _ => wrong name end)
  else if called "fold" then on [true] (fun o args => match o, args with
    | Some x, [_; f] => apply_fn f [x]
    | None, [d; _] => apply_fn d []
    | _, _ => wrong name end)
  else if called "toList" then on [] (fun o _ => oret (VList (match o with Some x => [x] | None => [] end)))
  else None.

(** A method of an `Either`. *)
Definition either_method (name : string) : option (list bool * Run) :=
  let called (n : string) := String.eqb name n in
  let on (lazy : list bool) (f : bool -> val -> list val -> X val) : option (list bool * Run) :=
    Some (lazy, fun _ v _ args => match v with
      | VObj (Data c [x]) => f (String.eqb c c_right) x args
      | _ => wrong name end) in
  if called "isLeft" then on [] (fun right _ _ => oret (VBool (negb right)))
  else if called "isRight" then on [] (fun right _ _ => oret (VBool right))
  else if called "getOrElse" then on [true] (fun right x args => match args with
    | [d] => if right then oret x else apply_fn d []
    | _ => wrong name end)
  else if called "map" then on [] (fun right x args => match args with
    | [f] => if right then y <~ apply_fn f [x] ;; oret (vdata c_right [y]) else oret (vdata c_left [x])
    | _ => wrong name end)
  else if called "left" then on [] (fun right x _ => oret (vdata "scala.util.Either$.LeftProjection"
    [vdata (if right then c_right else c_left) [x]]))
  else if called "fold" then on [] (fun right x args => match args with
    | [f; g] => apply_fn (if right then g else f) [x]
    | _ => wrong name end)
  else None.

(** ** The JDK

    An object of a class of the JDK is a reference with its class. A call of a method its protocol knows
    (`Jdk.v`) is one step of the machine (`ExtCall`), and nothing more is assumed of it. A thread is the
    machine's own. What takes a function of the program (a traversal, `updateAndGet`) is the loop the class
    documents, over the protocol's steps: the function's steps are the program's, among other threads'. *)

(** An exception a method gave, as a value: one that is an object of the program is that object. *)
Definition back (x : exn) : X val :=
  match x with
  | Thrown r => cls <~ oop (ObjClass r) ;; oret (vref cls r)
  | _ => oret (VExn x)
  end.

Definition given (v : val) : X val := match v with VExn x => back x | _ => oret v end.

(** A method of an object of the JDK. *)
Definition ext_call (r : nat) (name : string) (args : list val) : X val :=
  v <~ oop (ExtCall r name args) ;; given v.

(** A loop: `body` gives the next state, or the result. *)
Definition oloop {S : Type} (body : S -> X (S + val)) (s : S) : X val :=
  Iter (fun s => pbind (body s) (fun o => match o with
    | Ok (inl s') => Ret (inl s')
    | Ok (inr v) => Ret (inr (Ok v))
    | Exc x => Ret (inr (Exc x))
    | Brk v from => Ret (inr (Brk v from))
    end)) s (fun r => Ret r).

(** A traversal of a concurrent set: one element at a time, by its protocol's `next`. *)
Definition traverse (r : nat) (f : val -> X val) : X val :=
  oloop (fun passed : list val =>
    x <~ oop (ExtCall r "next" [VList passed]) ;;
    match x with
    | VObj (Data _ [a]) => b <~ given a ;; _ <~ f b ;; oret (inl (a :: passed))
    | _ => oret (inr VUnit)
    end) [].

Definition unit_of (m : X unit) : X val := _ <~ m ;; oret VUnit.
Definition truth_of (m : X bool) : X val := b <~ m ;; oret (VBool b).

(** Threads, and what else is the machine's own. *)
Definition threads (owner name : string) : option Run :=
  let at_ (cls : string) := String.eqb owner cls in
  let called (n : string) := String.eqb name n in
  let known (names : list string) := existsb (String.eqb name) names in
  let run (f : val -> list ty -> list val -> X val) : option Run := Some (fun _ v ts args => f v ts args) in
  if at_ "java.lang.Thread$" && called "currentThread" then run (fun _ _ _ => t <~ oop CurrentThread ;; oret (VTid t))
  else if at_ "java.lang.Thread$" && called "sleep" then run (fun _ _ _ => unit_of (oop ThreadSleep))
  else if at_ "java.lang.Thread$" && called "interrupted" then run (fun _ _ _ => truth_of (oop ThreadInterrupted))
  else if at_ "java.lang.Thread$" && called "yield" then run (fun _ _ _ => unit_of (oop ThreadYield))
  else if at_ "java.lang.Thread$" && called "ofVirtual" then
    run (fun _ _ _ => oret (VObj (Module "java.lang.Thread$.Builder")))
  else if at_ "java.lang.Thread$.Builder" && called "factory" then
    run (fun _ _ _ => oret (VObj (Module "java.util.concurrent.ThreadFactory")))
  else if at_ "java.util.concurrent.ThreadFactory" && called "newThread" then run (fun _ _ args => match args with
    | [VCode c] => t <~ oop (NewThread c) ;; oret (VTid t)
    | [VObj (Ref cls r)] =>
        t <~ oop (NewThread (Bound (Member "java.lang.Runnable" "run" ":scala.Unit") (vref cls r))) ;; oret (VTid t)
    | _ => wrong "newThread" end)
  else if at_ "java.lang.Thread" && known ["start"; "interrupt"; "join"; "getName"] then
    run (fun v _ _ => match v with
      | VTid u =>
          if called "start" then unit_of (oop (ThreadStart u))
          else if called "interrupt" then unit_of (oop (ThreadInterrupt u))
          else if called "join" then unit_of (oop (ThreadJoin u))
          else oret (VObj Text)
      | _ => wrong name end)
  else if at_ "java.util.concurrent.locks.LockSupport$" && called "park" then run (fun _ _ _ => unit_of (oop Park))
  else if at_ "java.lang.System$" && called "nanoTime" then run (fun _ _ _ => z <~ oop NanoTime ;; oret (vlong z))
  else None.

Definition traversed (owner : string) : bool :=
  String.eqb owner "java.lang.Iterable" || String.eqb owner "java.util.Set" || String.eqb owner "java.util.Collection"
  || String.eqb owner (p_class concurrent_set) || String.eqb owner "java.util.concurrent.ConcurrentHashMap$.CollectionView".

Definition jdk (owner name : string) : option Run :=
  let at_ (cls : string) := String.eqb owner cls in
  let called (n : string) := String.eqb name n in
  let run (f : val -> list ty -> list val -> X val) : option Run := Some (fun _ v ts args => f v ts args) in
  let made (p : protocol) : option Run :=
    run (fun _ _ args => r <~ oop (ExtNew p args) ;; oret (vref (p_class p) r)) in
  match threads owner name with
  | Some r => Some r
  | None =>
      if called "<init>" then match class_named owner with Some p => made p | None => None end
      else if at_ "java.util.concurrent.ConcurrentHashMap$" && called "newKeySet" then
        run (fun _ _ _ => r <~ oop (ExtNew concurrent_set []) ;; oret (vref (p_class concurrent_set) r))
      else if at_ (p_class atomic_reference) && called "updateAndGet" then
        (* the JDK's loop: read, apply, compare and set; again if another thread came between *)
        run (fun v _ args => match v, args with
          | VObj (Ref _ r), [f] =>
              oloop (fun _ : unit =>
                cur <~ ext_call r "get" [] ;;
                next <~ apply_fn f [cur] ;;
                done <~ oop (ExtCall r "compareAndSet" [cur; next]) ;;
                oret (match done with VBool true => inr next | _ => inl tt end)) tt
          | _, _ => wrong name end)
      else if traversed owner && called "forEach" then
        run (fun v _ args => match v, args with
          | VObj (Ref _ r), [f] => traverse r (fun x => apply_fn f [x])
          | _, _ => wrong name end)
      else if at_ "java.lang.Throwable" && called "addSuppressed" then
        (* not modelled: an exception keeps no other *)
        run (fun v _ args => match as_exn v, args with
          | Some _, [x] => match as_exn x with Some _ => oret VUnit | None => wrong name end
          | _, _ => wrong name end)
      else if at_ "java.lang.Throwable" && called "getCause" then run (fun v _ _ => match v with
        | VExn (ExecutionException cause) => back cause
        | _ => oret vnull end)
      else match class_with owner name with
        | Some _ => run (fun v _ args => match v with
            | VObj (Ref _ r) => ext_call r name args
            | _ => wrong name end)
        | None => None
        end
  end.

(** ** Arrays

    An array is an object of the JVM that can be written: a place per index, and its length. *)

Definition h_array := "scala.Array".

Fixpoint indexed (i : nat) (xs : list val) : list (string * val) :=
  match xs with
  | [] => []
  | x :: rest => (nat_text i, x) :: indexed (S i) rest
  end.

Definition new_array (xs : list val) : X val :=
  r <~ oop (ObjNew h_array (("length", vint (Z.of_nat (List.length xs))) :: indexed 0 xs)) ;; oret (vref h_array r).

Fixpoint array_elems (r : nat) (n i : nat) : X (list val) :=
  match n with
  | 0 => oret []
  | S n' => x <~ oop (ObjGet r (nat_text i)) ;; rest <~ array_elems r n' (S i) ;; oret (x :: rest)
  end.

Definition array_length (r : nat) : X Z :=
  n <~ oop (ObjGet r "length") ;; match n with VObj (Int z) => oret z | _ => wrong "length" end.

Definition array (owner name : string) : option Run :=
  let called (n : string) := String.eqb name n in
  let out_of_bounds : X val := othrow (Machine.Other "java.lang.ArrayIndexOutOfBoundsException") in
  if String.eqb owner "scala.Array$" && called "apply" then Some (fun _ _ _ args => match args with
    | VList xs :: _ => new_array xs
    | _ => wrong name end)
  else if String.eqb owner h_array then Some (fun _ v _ args => match v, args with
    | VObj (Ref _ r), [] =>
        n <~ array_length r ;;
        if called "length" then oret (vint n)
        else if called "clone" then xs <~ array_elems r (Z.to_nat n) 0 ;; new_array xs
        else wrong name
    | VObj (Ref _ r), [VObj (Int i)] =>
        n <~ array_length r ;;
        if called "apply" then
          if (0 <=? i)%Z && (i <? n)%Z then oop (ObjGet r (nat_text (Z.to_nat i))) else out_of_bounds
        else wrong name
    | VObj (Ref _ r), [VObj (Int i); x] =>
        n <~ array_length r ;;
        if called "update" then
          if (0 <=? i)%Z && (i <? n)%Z then unit_of (oop (ObjSet r (nat_text (Z.to_nat i)) x)) else out_of_bounds
        else wrong name
    | _, _ => wrong name end)
  else None.

(** ** Numbers, truth values, texts *)

Definition number (name : string) (a b : val) : option val :=
  let called (n : string) := String.eqb name n in
  let both (f : Z -> Z -> Z) (x y : Z) (long : bool) : option val :=
    Some (if long then long_of (f x y) else int_of (f x y)) in
  let test (f : Z -> Z -> bool) (x y : Z) : option val := Some (VBool (f x y)) in
  let go (x y : Z) (long : bool) : option val :=
    if called "+" then both Z.add x y long
    else if called "-" then both Z.sub x y long
    else if called "*" then both Z.mul x y long
    else if called "/" then (if Z.eqb y 0%Z then None else both Z.quot x y long)
    else if called "%" then (if Z.eqb y 0%Z then None else both Z.rem x y long)
    else if called "<" then test Z.ltb x y
    else if called "<=" then test Z.leb x y
    else if called ">" then test Z.gtb x y
    else if called ">=" then test Z.geb x y
    else if called "==" then test Z.eqb x y
    else if called "!=" then test (fun p q => negb (Z.eqb p q)) x y
    else if called "max" then both Z.max x y long
    else if called "min" then both Z.min x y long
    else None in
  match a, b with
  | VObj (Int x), VObj (Int y) => go x y false
  | VObj (Int x), VObj (Long y) | VObj (Long x), VObj (Int y) | VObj (Long x), VObj (Long y) => go x y true
  | _, _ => None
  end.

Definition scalar (owner name : string) : option (list bool * Run) :=
  let at_ (cls : string) := String.eqb owner cls in
  let called (n : string) := String.eqb name n in
  let known (names : list string) := existsb (String.eqb name) names in
  if (at_ "scala.Int" || at_ "scala.Long") && known ["+"; "-"; "*"; "/"; "%"; "<"; "<="; ">"; ">="; "=="; "!=";
      "max"; "min"; "unary_-"; "toLong"; "toInt"] then
    Some ([], fun _ v _ args => match args with
      | [w] => match number name v w with
          | Some r => oret r
          | None => if called "/" || called "%" then othrow (Machine.Other "java.lang.ArithmeticException") else wrong name
          end
      | [] => match v with
          | VObj (Int x) =>
              if called "unary_-" then oret (int_of (- x)%Z) else if called "toLong" then oret (vlong x)
              else if called "toInt" then oret v else wrong name
          | VObj (Long x) =>
              if called "unary_-" then oret (long_of (- x)%Z) else if called "toInt" then oret (int_of x)
              else if called "toLong" then oret v else wrong name
          | _ => wrong name end
      | _ => wrong name end)
  else if at_ "scala.Boolean" then
    if called "&&" then Some ([true], fun _ v _ args => match v, args with
      | VBool true, [d] => apply_fn d []
      | VBool false, [_] => oret (VBool false)
      | _, _ => wrong name end)
    else if called "||" then Some ([true], fun _ v _ args => match v, args with
      | VBool false, [d] => apply_fn d []
      | VBool true, [_] => oret (VBool true)
      | _, _ => wrong name end)
    else if called "unary_!" then Some ([], fun _ v _ _ => match v with
      | VBool b => oret (VBool (negb b))
      | _ => wrong name end)
    else if called "==" then Some ([], fun _ v _ args => match v, args with
      | VBool a, [VBool b] => oret (VBool (Bool.eqb a b))
      | _, _ => wrong name end)
    else if called "!=" then Some ([], fun _ v _ args => match v, args with
      | VBool a, [VBool b] => oret (VBool (negb (Bool.eqb a b)))
      | _, _ => wrong name end)
    else None
  else if at_ "java.lang.String" && called "+" then
    Some ([], fun _ v _ args => match v, args with
      | VObj (Str a), [VObj (Str b)] => oret (vstr (String.append a b))
      | _, [_] => oret (VObj Text)
      | _, _ => wrong name end)
  else if at_ "scala.StringContext$" && called "apply" then Some ([], fun _ _ _ _ => oret (VObj Text))
  else if at_ "scala.StringContext" && called "s" then Some ([], fun _ _ _ _ => oret (VObj Text))
  else None.

(** ** Data made and taken apart *)

Definition product (owner name : string) : option Run :=
  let at_ (cls : string) := String.eqb owner cls in
  let called (n : string) := String.eqb name n in
  let made (c : string) : option Run :=
    if called "apply" then Some (fun _ _ _ args => oret (vdata c args))
    else if called "unapply" then Some (fun _ _ _ args => match args with [x] => oret x | _ => wrong name end)
    else None in
  let part (i : nat) : option Run := Some (fun _ v _ _ => match v with
    | VObj (Data _ xs) => match nth_error xs i with Some x => oret x | None => wrong name end
    | _ => wrong name end) in
  if at_ "scala.Some$" then made c_some
  else if at_ "scala.util.Left$" then made c_left
  else if at_ "scala.util.Right$" then made c_right
  else if at_ "scala.util.Success$" then made c_success
  else if at_ "scala.util.Failure$" then made c_failure
  else if at_ "scala.Tuple2$" then made (tuple 2)
  else if at_ "scala.Tuple3$" then made (tuple 3)
  else if at_ "scala.Tuple4$" then made (tuple 4)
  else if at_ "scala.Tuple2" || at_ "scala.Tuple3" || at_ "scala.Tuple4" || at_ "scala.Some" || at_ c_left
      || at_ c_right then
    if called "_1" || called "value" then part 0 else if called "_2" then part 1
    else if called "_3" then part 2 else if called "_4" then part 3 else None
  else if at_ "scala.collection.immutable.::$" then
    if called "apply" then Some (fun _ _ _ args => match args with
      | [x; VList xs] => oret (VList (x :: xs))
      | _ => wrong name end)
    else if called "unapply" then Some (fun _ _ _ args => match args with [x] => oret x | _ => wrong name end)
    else None
  else if at_ "scala.Option$" && called "apply" then Some (fun _ _ _ args => match args with
    | [VObj Null] => oret none
    | [x] => oret (some x)
    | _ => wrong name end)
  else if at_ "scala.Option$" && called "empty" then Some (fun _ _ _ _ => oret none)
  else if at_ "scala.util.Try" && called "get" then Some (fun _ v _ _ => match v with
    | VObj (Data c [x]) =>
        if String.eqb c c_success then oret x
        else match as_exn x with Some e => othrow e | None => wrong name end
    | _ => wrong name end)
  else None.

(** A collection made by its companion: `List(…)`, `Vector.empty`, `Set.empty`, `Map.empty`. *)
Definition factory (name : string) : option Run :=
  let made (on : val) (xs : list val) : val :=
    match on with
    | VObj (Module m) =>
        let has (part : string) := match index 0 part m with Some _ => true | None => false end in
        if has "Vector" then vdata c_vector [VList xs]
        else if has "Set" then vdata c_set [VList xs]
        else if has "Map" then vdata c_map [VList xs]
        else VList xs
    | _ => VList xs
    end in
  if String.eqb name "empty" then Some (fun _ v _ _ => oret (made v []))
  else if String.eqb name "apply" then Some (fun _ v _ args => match args with
    | [VList xs] => oret (made v xs)
    | _ => wrong name end)
  else None.

(** ** What is named and not called: an object of the library, a constant *)

Definition constant (owner name : string) : option val :=
  let at_ (cls : string) := String.eqb owner cls in
  let called (n : string) := String.eqb name n in
  if at_ "scala" && called "None" then Some none
  else if at_ "scala.package$" && called "Nil" then Some (VList [])
  else if at_ "scala.package$" && called "List" then Some (VObj (Module "scala.collection.immutable.List$"))
  else if at_ "scala.package$" && called "Vector" then Some (VObj (Module "scala.collection.immutable.Vector$"))
  else if at_ "scala.package$" && called "Seq" then Some (VObj (Module "scala.collection.immutable.List$"))
  else if at_ "scala.Predef$" && called "Set" then Some (VObj (Module "scala.collection.immutable.Set$"))
  else if at_ "scala.Predef$" && called "Map" then Some (VObj (Module "scala.collection.immutable.Map$"))
  else if at_ "scala.concurrent.duration.Duration$" && called "Inf" then Some (vdata c_forever [])
  else if at_ "scala.compiletime.package$package$" && called "uninitialized" then Some vnull
  else None.

(** ** The rest: functions applied, exceptions made and thrown, what is not fatal, durations *)

Definition misc (owner name : string) : option (list bool * Run) :=
  let at_ (cls : string) := String.eqb owner cls in
  let called (n : string) := String.eqb name n in
  let plain (f : Run) : option (list bool * Run) := Some ([], f) in
  if called "apply" && (at_ "scala.Function0" || at_ "scala.Function1" || at_ "scala.Function2"
      || at_ "scala.Function3" || at_ "scala.ContextFunction1" || at_ "scala.ContextFunction2") then
    plain (fun _ v _ args => apply_fn v args)
  else if at_ "java.lang.Runnable" && called "run" then plain (fun _ v _ _ => apply_fn v [])
  else if at_ "<special-ops>" && called "throw" then plain (fun _ _ _ args => match args with
    | [x] => match as_exn x with Some e => othrow e | None => wrong "a throw of what is no exception" end
    | _ => wrong name end)
  else if called "<init>" && (existsb (String.eqb "java.lang.Throwable") (supers owner)
      || at_ "java.lang.Throwable") then
    plain (fun _ _ _ _ => oret (VExn (made_exn owner)))
  else if at_ "java.lang.Object" && called "<init>" then plain (fun _ _ _ _ => oret VUnit)
  else if at_ "scala.util.control.NonFatal$" && called "unapply" then plain (fun _ _ _ args => match args with
    | [VExn InterruptedException] => oret none
    | [x] => oret (some x)
    | _ => wrong name end)
  else if at_ "scala.util.control.NonFatal$" && called "apply" then plain (fun _ _ _ args => match args with
    | [VExn InterruptedException] => oret (VBool false)
    | [_] => oret (VBool true)
    | _ => wrong name end)
  else if at_ "scala.Predef$" && called "println" then plain (fun _ _ _ _ => oret VUnit)
  else if at_ "scala.Predef$" && called "identity" then plain (fun _ _ _ args => match args with
    | [x] => oret x
    | _ => wrong name end)
  else if at_ "scala.Predef$" && called "classOf" then plain (fun _ _ ts _ => match ts with
    | [t] => match ty_class t with Some c => oret (VObj (ClassOf c)) | None => wrong name end
    | _ => wrong name end)
  else if at_ "java.lang.Class" && called "isInstance" then plain (fun ctx v _ args => match v, args with
    | VObj (ClassOf c), [x] => match c_isa ctx x c with
        | Some b => oret (VBool b)
        | None => wrong "a test of a class on a value whose class is not known" end
    | _, _ => wrong name end)
  else if at_ "scala.reflect.ClassTag$" && called "apply" then plain (fun _ _ _ args => match args with
    | [x] => oret (vdata "scala.reflect.ClassTag" [x])
    | _ => wrong name end)
  else if at_ "scala.reflect.ClassTag" && called "runtimeClass" then plain (fun _ v _ _ => match v with
    | VObj (Data _ [x]) => oret x
    | _ => wrong name end)
  else if at_ "scala.concurrent.duration.package$" && called "DurationLong" then
    plain (fun _ _ _ args => match args with [x] => oret x | _ => wrong name end)
  else if at_ "scala.concurrent.duration.package$" && called "DurationInt" then
    plain (fun _ _ _ args => match args with [VObj (Int x)] => oret (vlong x) | _ => wrong name end)
  else if at_ "scala.concurrent.duration.DurationConversions" then
    let scaled (factor : Z) : option (list bool * Run) := plain (fun _ v _ _ => match v with
      | VObj (Long x) | VObj (Int x) => oret (vdata c_duration [long_of (x * factor)%Z])
      | _ => wrong name end) in
    if called "nanos" || called "nanoseconds" || called "nano" || called "nanosecond" then scaled 1%Z
    else if called "micros" || called "microseconds" || called "micro" || called "microsecond" then scaled 1000%Z
    else if called "millis" || called "milliseconds" || called "milli" || called "millisecond" then
      scaled 1000000%Z
    else if called "seconds" || called "second" then scaled 1000000000%Z
    else if called "minutes" || called "minute" then scaled 60000000000%Z
    else if called "hours" || called "hour" then scaled 3600000000000%Z
    else if called "days" || called "day" then scaled 86400000000000%Z
    else None
  else if (at_ "scala.concurrent.duration.Duration" || at_ c_duration)
      && (called "toMillis" || called "toNanos" || called "isFinite") then
    plain (fun _ v _ _ => match v with
      | VObj (Data _ [VObj (Long ns)]) =>
          if called "toMillis" then oret (long_of (Z.quot ns 1000000%Z))
          else if called "toNanos" then oret (vlong ns)
          else if called "isFinite" then oret (VBool true)
          else wrong name
      | VObj (Data _ []) => if called "isFinite" then oret (VBool false) else wrong name
      | _ => wrong name end)
  else if at_ "scala.util.Either$.LeftProjection" && called "getOrElse" then
    Some ([true], fun _ v _ args => match v, args with
      | VObj (Data _ [VObj (Data c [x])]), [d] => if String.eqb c c_left then oret x else apply_fn d []
      | _, _ => wrong name end)
  else if at_ "scala.runtime.ScalaRunTime$" && called "_toString" then plain (fun _ _ _ _ => oret (VObj Text))
  else if called "toString" then plain (fun _ _ _ _ => oret (VObj Text))
  else None.

(** ** What a definition from outside does

    The JDK's by its contract; a concurrent set's by what it holds; a collection's by its name; then the data
    and the rest. What is only named (an object of the library) is a name. *)

Definition is_collection (owner : string) : bool := String.prefix "scala.collection" owner.

Definition outside (owner name : string) : option primitive :=
  let plain (r : Run) : option primitive := Some (Prim [] r) in
  let lazy (p : list bool * Run) : option primitive := Some (Prim (fst p) (snd p)) in
  match jdk owner name with
  | Some r => plain r
  | None =>
  match array owner name with
  | Some r => plain r
  | None =>
  match product owner name with
  | Some r => plain r
  | None =>
  match constant owner name with
  | Some v => plain (fun _ _ _ _ => oret v)
  | None =>
  match scalar owner name with
  | Some p => lazy p
  | None =>
  match (if String.eqb owner "scala.Option" || String.eqb owner c_some || String.eqb owner c_none
         then option_method name else None) with
  | Some p => lazy p
  | None =>
  match (if String.eqb owner "scala.util.Either" || String.eqb owner c_left || String.eqb owner c_right
         then either_method name else None) with
  | Some p => lazy p
  | None =>
  match misc owner name with
  | Some p => lazy p
  | None =>
  if is_collection owner then
    match factory name, map_method name, collection name with
    | None, None, None => None
    | _, _, _ =>
        Some (Prim [] (fun ctx v ts args =>
          match v with
          | VObj (Module _) => match factory name with Some r => r ctx v ts args | None => wrong name end
          | _ =>
              match (if is_map v then map_method name else None) with
              | Some r => r ctx v ts args
              | None => match collection name with Some r => r ctx v ts args | None => wrong name end
              end
          end))
    end
  else None
  end end end end end end end end.
