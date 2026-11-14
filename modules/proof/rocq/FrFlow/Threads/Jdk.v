(** The JDK's classes as Ox uses them: each class's state, and for each method a contract.

    These are the assumptions every proof about Ox rests on. A contract says what one call of a method may do:
    what it may return, how it may leave its object, and when it may return at all (a blocking method has no step
    until then). A call is one step among the steps of other threads: that is the assumption that the method is
    linearizable, taken of every method here. Where the JDK's documentation promises less than a simple reading
    would, the contract allows more behaviours, so that what is proven holds of every JDK that keeps its
    documentation. Each contract names where the promise is made.

    Not modelled: integer overflow, a thread ended from outside (`Thread.stop`), errors of the JVM itself
    (`OutOfMemoryError`, `StackOverflowError`), a `Throwable`'s identity and its suppressed exceptions. *)

From Stdlib Require Import ZArith List Bool String.
Import ListNotations.

Set Implicit Arguments.
Set Warnings "-register-all".

Definition tid := nat.

(** What can be thrown. *)
Inductive exn :=
  | InterruptedException
  | ExecutionException (cause : exn)
  | IllegalStateException
  | IllegalThreadStateException
  | NullPointerException
  | NoSuchElementException
  | Other (class : string)               (* a throwable of another class of the code read *)
  | Thrown (n : nat).                    (* any other throwable: the caller's own *)

Section Jdk.

  (** What is not the JDK's: the closures a program makes (`code`), and the objects of the code that is read
      (`obj`). *)
  Variables code obj : Type.

  (** A value held where Java's type is a type parameter. *)
  Inductive val :=
    | VUnit
    | VBool (b : bool)
    | VTid (t : tid)
    | VExn (e : exn)
    | VObj (o : obj)
    | VCode (c : code)
    | VList (vs : list val)
    | VAny (n : nat).                    (* the caller's own data *)

  (** ** The state of each class *)

  Inductive tstatus := TNew | TStarted | TTerminated.

  (** java.lang.Thread: what it runs, where it is in its life, its interrupt status. *)
  Record thread := Thread { t_code : code; t_status : tstatus; t_intr : bool }.

  Record jst := Jst {
    j_th : tid -> option thread;                 (* java.lang.Thread *)
    j_ab : nat -> option bool;                   (* java.util.concurrent.atomic.AtomicBoolean *)
    j_ai : nat -> option Z;                      (* java.util.concurrent.atomic.AtomicInteger *)
    j_cf : nat -> option (option (exn + val));   (* java.util.concurrent.CompletableFuture: not completed, or how *)
    j_ts : nat -> option (tid -> bool);          (* ConcurrentHashMap.newKeySet[Thread] *)
    j_es : nat -> option (list exn);             (* ConcurrentHashMap.newKeySet[Throwable] *)
    j_vs : nat -> option (list val);             (* ConcurrentHashMap.newKeySet[E] *)
    j_ar : nat -> option (option val);           (* java.util.concurrent.atomic.AtomicReference; `None` is null *)
    j_tl : nat -> tid -> option val;             (* java.lang.ThreadLocal, per thread; `None` is null *)
    j_sem : nat -> option nat;                   (* java.util.concurrent.Semaphore: its permits *)
    j_bq : nat -> option (nat * list val);       (* java.util.concurrent.ArrayBlockingQueue: capacity, elements *)
    j_obj : nat -> option (string * list (string * val)) }.  (* an object of the code read: its class, its fields *)

  Definition upd {B : Type} (f : nat -> B) (k : nat) (v : B) : nat -> B :=
    fun x => if Nat.eq_dec x k then v else f x.

  Definition set_th σ u th := Jst (upd (j_th σ) u (Some th)) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_ab σ r b := Jst (j_th σ) (upd (j_ab σ) r (Some b)) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_ai σ r z := Jst (j_th σ) (j_ab σ) (upd (j_ai σ) r (Some z)) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_cf σ r c := Jst (j_th σ) (j_ab σ) (j_ai σ) (upd (j_cf σ) r (Some c)) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_ts σ r s := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (upd (j_ts σ) r (Some s)) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_es σ r s := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (upd (j_es σ) r (Some s)) (j_vs σ) (j_ar σ) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_vs σ r s := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (upd (j_vs σ) r (Some s)) (j_ar σ) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_ar σ r v := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (upd (j_ar σ) r (Some v)) (j_tl σ) (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_tl σ r t v := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ)
    (fun r' t' => if Nat.eq_dec r' r then (if Nat.eq_dec t' t then v else j_tl σ r' t') else j_tl σ r' t')
    (j_sem σ) (j_bq σ) (j_obj σ).
  Definition set_sem σ r n := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ)
    (upd (j_sem σ) r (Some n)) (j_bq σ) (j_obj σ).
  Definition set_bq σ r q := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ)
    (j_sem σ) (upd (j_bq σ) r (Some q)) (j_obj σ).
  Definition set_obj σ r o := Jst (j_th σ) (j_ab σ) (j_ai σ) (j_cf σ) (j_ts σ) (j_es σ) (j_vs σ) (j_ar σ) (j_tl σ)
    (j_sem σ) (j_bq σ) (upd (j_obj σ) r (Some o)).

  (** A field of an object, and the fields with one given a value. *)
  Fixpoint field (fields : list (string * val)) (name : string) : option val :=
    match fields with
    | [] => None
    | (n, v) :: rest => if String.eqb n name then Some v else field rest name
    end.
  Fixpoint with_field (fields : list (string * val)) (name : string) (v : val) : list (string * val) :=
    match fields with
    | [] => [(name, v)]
    | (n, v0) :: rest => if String.eqb n name then (n, v) :: rest else (n, v0) :: with_field rest name v
    end.

  Definition interrupted σ (t : tid) : bool :=
    match j_th σ t with Some th => t_intr th | None => false end.

  (** The caller's interrupt status cleared, as a method that throws `InterruptedException` leaves it. *)
  Definition clear_intr σ (t : tid) : jst :=
    match j_th σ t with Some th => set_th σ t (Thread (t_code th) (t_status th) false) | None => σ end.

  (** ** The methods *)

  (** A method call, typed by what it gives: an exception or a result. *)
  Inductive op : Type -> Type :=
    (* java.lang.Thread, java.util.concurrent.ThreadFactory *)
    | CurrentThread : op (exn + tid)                         (* Thread.currentThread() *)
    | NewThread (c : code) : op (exn + tid)                  (* ThreadFactory.newThread(runnable) *)
    | ThreadStart (u : tid) : op (exn + unit)                (* thread.start() *)
    | ThreadInterrupt (u : tid) : op (exn + unit)            (* thread.interrupt() *)
    | ThreadJoin (u : tid) : op (exn + unit)                 (* thread.join() *)
    | ThreadSleep : op (exn + unit)                          (* Thread.sleep(millis) *)
    (* AtomicBoolean *)
    | AbNew (b : bool) : op (exn + nat)
    | AbGet (r : nat) : op (exn + bool)
    | AbSet (r : nat) (b : bool) : op (exn + unit)
    | AbGetAndSet (r : nat) (b : bool) : op (exn + bool)
    (* AtomicInteger *)
    | AiNew (z : Z) : op (exn + nat)
    | AiIncrementAndGet (r : nat) : op (exn + Z)
    | AiDecrementAndGet (r : nat) : op (exn + Z)
    (* CompletableFuture *)
    | CfNew : op (exn + nat)
    | CfComplete (r : nat) (v : val) : op (exn + bool)
    | CfCompleteExceptionally (r : nat) (e : exn) : op (exn + bool)
    | CfGet (r : nat) : op (exn + val)
    | CfIsCompletedExceptionally (r : nat) : op (exn + bool)
    | CfExceptionNow (r : nat) : op (exn + exn)
    (* a concurrent set of threads *)
    | TsNew : op (exn + nat)
    | TsAdd (r : nat) (u : tid) : op (exn + bool)
    | TsRemove (r : nat) (u : tid) : op (exn + bool)
    | TsContains (r : nat) (u : tid) : op (exn + bool)
    | TsIsEmpty (r : nat) : op (exn + bool)
    | TsNext (r : nat) (seen : list tid) : op (exn + option tid)   (* one element of a traversal *)
    (* a concurrent set of exceptions, and one of values *)
    | EsNew : op (exn + nat)
    | EsAdd (r : nat) (e : exn) : op (exn + bool)
    | EsNext (r : nat) (seen : list exn) : op (exn + option exn)
    | VsNew : op (exn + nat)
    | VsAdd (r : nat) (v : val) : op (exn + bool)
    | VsNext (r : nat) (seen : list val) : op (exn + option val)
    (* AtomicReference *)
    | ArNew (v : option val) : op (exn + nat)
    | ArGet (r : nat) : op (exn + option val)
    | ArGetAndSet (r : nat) (v : option val) : op (exn + option val)
    | ArUpdateAndGet (r : nat) (f : option val -> exn + option val) : op (exn + option val)
    (* ThreadLocal *)
    | TlGet (r : nat) : op (exn + option val)
    | TlSet (r : nat) (v : option val) : op (exn + unit)
    (* Throwable *)
    | AddSuppressed (e e' : exn) : op (exn + unit)
    (* a call of code that is not read and is taken to touch nothing here: it gives anything *)
    | Extern (X : Type) (name : string) : op (exn + X)
    (* a cast the compiler made: the JVM's type safety says it does not fail *)
    | TypeError (X : Type) : op X
    (* code that is not read: it may do anything *)
    | Chaos (X : Type) (what : string) : op X
    (* java.lang.Thread, LockSupport, System *)
    | ThreadInterrupted : op (exn + bool)                    (* Thread.interrupted() *)
    | ThreadYield : op (exn + unit)                          (* Thread.yield() *)
    | Park : op (exn + unit)                                 (* LockSupport.park() *)
    | NanoTime : op (exn + Z)                                (* System.nanoTime() *)
    (* Semaphore *)
    | SemNew (permits : nat) : op (exn + nat)
    | SemAcquire (r : nat) : op (exn + unit)
    | SemRelease (r : nat) : op (exn + unit)
    (* ArrayBlockingQueue *)
    | BqNew (capacity : nat) : op (exn + nat)
    | BqPut (r : nat) (v : val) : op (exn + unit)
    | BqTake (r : nat) : op (exn + val)
    (* an object of the code read: made, a field read, a field assigned, its class *)
    | ObjNew (cls : string) (fields : list (string * val)) : op (exn + nat)
    | ObjGet (r : nat) (name : string) : op (exn + val)
    | ObjSet (r : nat) (name : string) (v : val) : op (exn + unit)
    | ObjClass (r : nat) : op (exn + string)
    (* AtomicReference.compareAndSet, as `updateAndGet` uses it *)
    | ArCas (r : nat) (expected new : option val) : op (exn + bool).

  (** What one call may do, made by thread `t` in state `σ`: its result and the state it leaves. No step: the
      call does not return yet. *)
  Definition opstep (t : tid) (X : Type) (o : op X) : jst -> X -> jst -> Prop :=
    match o in op X return jst -> X -> jst -> Prop with

    (* Thread.currentThread(): the caller. *)
    | CurrentThread => fun σ x σ' => x = inr t /\ σ' = σ

    (* ThreadFactory.newThread: a thread that did not exist, not started, not interrupted. *)
    | NewThread c => fun σ x σ' => exists u,
        j_th σ u = None /\ x = inr u /\ σ' = set_th σ u (Thread c TNew false)

    (* Thread.start: a thread not started starts; any other throws IllegalThreadStateException. *)
    | ThreadStart u => fun σ x σ' =>
        match j_th σ u with
        | Some (Thread c TNew i) => x = inr tt /\ σ' = set_th σ u (Thread c TStarted i)
        | _ => x = inl IllegalThreadStateException /\ σ' = σ
        end

    (* Thread.interrupt: the status of a started thread is set. Of a thread not alive the documentation says it
       "need not have any effect": it is set or left. *)
    | ThreadInterrupt u => fun σ x σ' => x = inr tt /\
        match j_th σ u with
        | Some (Thread c TStarted i) => σ' = set_th σ u (Thread c TStarted true)
        | Some (Thread c s i) => σ' = set_th σ u (Thread c s true) \/ σ' = σ
        | None => σ' = σ
        end

    (* Thread.join: returns once the thread is not alive (JLS 17.4.5: its actions come before the return); or the
       caller, interrupted, throws InterruptedException with its status cleared. *)
    | ThreadJoin u => fun σ x σ' =>
        (x = inr tt /\ σ' = σ /\
           match j_th σ u with Some (Thread _ TStarted _) => False | _ => True end) \/
        (x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)

    (* Thread.sleep: returns, or the caller, interrupted, throws. *)
    | ThreadSleep => fun σ x σ' =>
        (x = inr tt /\ σ' = σ) \/
        (x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)

    (* AtomicBoolean *)
    | AbNew b => fun σ x σ' => exists r, j_ab σ r = None /\ x = inr r /\ σ' = set_ab σ r b
    | AbGet r => fun σ x σ' => exists b, j_ab σ r = Some b /\ x = inr b /\ σ' = σ
    | AbSet r b => fun σ x σ' => j_ab σ r <> None /\ x = inr tt /\ σ' = set_ab σ r b
    | AbGetAndSet r b => fun σ x σ' => exists b0, j_ab σ r = Some b0 /\ x = inr b0 /\ σ' = set_ab σ r b

    (* AtomicInteger *)
    | AiNew z => fun σ x σ' => exists r, j_ai σ r = None /\ x = inr r /\ σ' = set_ai σ r z
    | AiIncrementAndGet r => fun σ x σ' => exists z, j_ai σ r = Some z /\ x = inr (z + 1)%Z /\ σ' = set_ai σ r (z + 1)%Z
    | AiDecrementAndGet r => fun σ x σ' => exists z, j_ai σ r = Some z /\ x = inr (z - 1)%Z /\ σ' = set_ai σ r (z - 1)%Z

    (* CompletableFuture: completed at most once; `complete` and `completeExceptionally` say whether theirs was
       the completion. *)
    | CfNew => fun σ x σ' => exists r, j_cf σ r = None /\ x = inr r /\ σ' = set_cf σ r None
    | CfComplete r v => fun σ x σ' =>
        match j_cf σ r with
        | Some None => x = inr true /\ σ' = set_cf σ r (Some (inr v))
        | Some (Some _) => x = inr false /\ σ' = σ
        | None => False
        end
    | CfCompleteExceptionally r e => fun σ x σ' =>
        match j_cf σ r with
        | Some None => x = inr true /\ σ' = set_cf σ r (Some (inl e))
        | Some (Some _) => x = inr false /\ σ' = σ
        | None => False
        end

    (* CompletableFuture.get: returns once completed, with the value, or throws ExecutionException over the
       cause; or the caller, interrupted, throws InterruptedException with its status cleared. *)
    | CfGet r => fun σ x σ' =>
        (exists v, j_cf σ r = Some (Some (inr v)) /\ x = inr v /\ σ' = σ) \/
        (exists e, j_cf σ r = Some (Some (inl e)) /\ x = inl (ExecutionException e) /\ σ' = σ) \/
        (j_cf σ r <> None /\ x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)
    | CfIsCompletedExceptionally r => fun σ x σ' => σ' = σ /\
        match j_cf σ r with
        | Some (Some (inl _)) => x = inr true
        | Some _ => x = inr false
        | None => False
        end
    | CfExceptionNow r => fun σ x σ' => σ' = σ /\
        match j_cf σ r with
        | Some (Some (inl e)) => x = inr e
        | Some _ => x = inl IllegalStateException
        | None => False
        end

    (* A concurrent set of threads: `add`, `remove` and `contains` each at one moment. *)
    | TsNew => fun σ x σ' => exists r, j_ts σ r = None /\ x = inr r /\ σ' = set_ts σ r (fun _ => false)
    | TsAdd r u => fun σ x σ' => exists s,
        j_ts σ r = Some s /\ x = inr (negb (s u)) /\ σ' = set_ts σ r (upd s u true)
    | TsRemove r u => fun σ x σ' => exists s,
        j_ts σ r = Some s /\ x = inr (s u) /\ σ' = set_ts σ r (upd s u false)
    | TsContains r u => fun σ x σ' => exists s, j_ts σ r = Some s /\ x = inr (s u) /\ σ' = σ

    (* isEmpty: `true` only of a set that is empty at that moment. ConcurrentHashMap's documentation does NOT
       promise this while other threads update the set ("not for program control"): this contract is stronger
       than the documentation, and the JDK does not keep it. `isEmpty` sums counters that the threads adding and
       removing are changing; with an element added by one thread and removed by another, JDK 21 answered `true`
       of a set that always held an element (`examples/ox/probe/IsEmptyProbe.scala`: 44 times of 717 million).
       What is proven from this contract is proven of a set whose emptiness test is exact. *)
    | TsIsEmpty r => fun σ x σ' => exists s, j_ts σ r = Some s /\ σ' = σ /\
        ((x = inr true /\ forall u, s u = false) \/ (x = inr false /\ exists u, s u = true))

    (* One element of a traversal (`forEach`). A weakly consistent traversal may or may not see what changes as it
       goes: it is taken to give any element not given before, or to end, at any time. *)
    | TsNext r seen => fun σ x σ' => j_ts σ r <> None /\ σ' = σ /\
        match x with inr (Some u) => ~ In u seen | inr None => True | inl _ => False end

    (* The other sets: only added to and traversed. *)
    | EsNew => fun σ x σ' => exists r, j_es σ r = None /\ x = inr r /\ σ' = set_es σ r []
    | EsAdd r e => fun σ x σ' => exists s b, j_es σ r = Some s /\ x = inr b /\ σ' = set_es σ r (e :: s)
    | EsNext r seen => fun σ x σ' => j_es σ r <> None /\ σ' = σ /\
        match x with inr (Some e) => ~ In e seen | inr None => True | inl _ => False end
    | VsNew => fun σ x σ' => exists r, j_vs σ r = None /\ x = inr r /\ σ' = set_vs σ r []
    | VsAdd r v => fun σ x σ' => exists s b, j_vs σ r = Some s /\ x = inr b /\ σ' = set_vs σ r (v :: s)
    | VsNext r seen => fun σ x σ' => j_vs σ r <> None /\ σ' = σ /\
        match x with inr (Some v) => ~ In v seen | inr None => True | inl _ => False end

    (* AtomicReference. `updateAndGet` applies a function without effects at one moment; what the function
       throws is thrown, the reference unchanged. *)
    | ArNew v => fun σ x σ' => exists r, j_ar σ r = None /\ x = inr r /\ σ' = set_ar σ r v
    | ArGet r => fun σ x σ' => exists v, j_ar σ r = Some v /\ x = inr v /\ σ' = σ
    | ArGetAndSet r v => fun σ x σ' => exists v0, j_ar σ r = Some v0 /\ x = inr v0 /\ σ' = set_ar σ r v
    | ArUpdateAndGet r f => fun σ x σ' => exists v0, j_ar σ r = Some v0 /\
        match f v0 with
        | inr v1 => x = inr v1 /\ σ' = set_ar σ r v1
        | inl e => x = inl e /\ σ' = σ
        end

    (* ThreadLocal: a thread reads what it set. *)
    | TlGet r => fun σ x σ' => x = inr (j_tl σ r t) /\ σ' = σ
    | TlSet r v => fun σ x σ' => x = inr tt /\ σ' = set_tl σ r t v

    (* Throwable.addSuppressed: not modelled. *)
    | AddSuppressed _ _ => fun σ x σ' => x = inr tt /\ σ' = σ

    (* Code not read, taken to touch nothing of this state (an `ErrorMode`'s methods, a `ForkLocalMap`'s). *)
    | Extern _ _ => fun σ x σ' => σ' = σ

    (* A failed cast: never. *)
    | TypeError _ => fun σ x σ' => False

    (* Code not read at all: any result, and any state in which the threads that had started still have (a
       thread is not ended from outside). A proof passes it only where it cannot be reached. *)
    | Chaos _ _ => fun σ x σ' => forall u,
        match j_th σ u with
        | Some (Thread _ TStarted _) => match j_th σ' u with Some (Thread _ TStarted _) => True | _ => False end
        | _ => True
        end

    (* Thread.interrupted(): the caller's status, cleared. *)
    | ThreadInterrupted => fun σ x σ' => x = inr (interrupted σ t) /\ σ' = clear_intr σ t

    (* Thread.yield(): a hint to the scheduler; nothing of the state. *)
    | ThreadYield => fun σ x σ' => x = inr tt /\ σ' = σ

    (* LockSupport.park(): returns when unparked, when the caller is interrupted, or "spuriously (that is, for no
       reason)": it is taken to return at any time. Its callers park in a loop. *)
    | Park => fun σ x σ' => x = inr tt /\ σ' = σ

    (* System.nanoTime(): some number. Nothing is assumed of time. *)
    | NanoTime => fun σ x σ' => exists z, x = inr z /\ σ' = σ

    (* Semaphore: `acquire` takes a permit once there is one, or the caller, interrupted, throws with its status
       cleared; `release` adds one. Each at one moment. *)
    | SemNew n => fun σ x σ' => exists r, j_sem σ r = None /\ x = inr r /\ σ' = set_sem σ r n
    | SemAcquire r => fun σ x σ' =>
        (exists n, j_sem σ r = Some (S n) /\ x = inr tt /\ σ' = set_sem σ r n) \/
        (j_sem σ r <> None /\ x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)
    | SemRelease r => fun σ x σ' => exists n, j_sem σ r = Some n /\ x = inr tt /\ σ' = set_sem σ r (S n)

    (* ArrayBlockingQueue: `put` adds at the end once there is room, `take` gives the first element once there
       is one; or the caller, interrupted, throws with its status cleared. Each at one moment. *)
    | BqNew c => fun σ x σ' => exists r, j_bq σ r = None /\ x = inr r /\ σ' = set_bq σ r (c, [])
    | BqPut r v => fun σ x σ' =>
        (exists c q, j_bq σ r = Some (c, q) /\ List.length q < c /\ x = inr tt /\
           σ' = set_bq σ r (c, (q ++ [v])%list)) \/
        (j_bq σ r <> None /\ x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)
    | BqTake r => fun σ x σ' =>
        (exists c v q, j_bq σ r = Some (c, v :: q) /\ x = inr v /\ σ' = set_bq σ r (c, q)) \/
        (j_bq σ r <> None /\ x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)

    (* An object of the code read: its fields are the JVM's heap. Each read and each assignment is one step:
       that is the reading the memory model gives code with no data race (JLS 17.4.5), which is checked of the
       code read, not assumed here. A field the object has not is no step. *)
    | ObjNew cls fields => fun σ x σ' => exists r, j_obj σ r = None /\ x = inr r /\ σ' = set_obj σ r (cls, fields)
    | ObjGet r name => fun σ x σ' => exists cls fields v,
        j_obj σ r = Some (cls, fields) /\ field fields name = Some v /\ x = inr v /\ σ' = σ
    | ObjSet r name v => fun σ x σ' => exists cls fields,
        j_obj σ r = Some (cls, fields) /\ x = inr tt /\ σ' = set_obj σ r (cls, with_field fields name v)
    | ObjClass r => fun σ x σ' => exists cls fields, j_obj σ r = Some (cls, fields) /\ x = inr cls /\ σ' = σ

    (* AtomicReference.compareAndSet: the reference is set if it holds what the caller read; and it may fail at
       any time, as an update that lost to another does. `updateAndGet` is the loop the JDK documents: read,
       apply the function, compare and set, again if that failed ("the function ... may be re-applied when
       attempted updates fail due to contention"). *)
    | ArCas r expected new => fun σ x σ' =>
        (j_ar σ r = Some expected /\ x = inr true /\ σ' = set_ar σ r new) \/
        (j_ar σ r <> None /\ x = inr false /\ σ' = σ)
    end.

End Jdk.

(** The closures and the objects are read off where an operation or a value is used. *)
Arguments CurrentThread {code obj}.
Arguments NewThread {code obj} c.
Arguments ThreadStart {code obj} u.
Arguments ThreadInterrupt {code obj} u.
Arguments ThreadJoin {code obj} u.
Arguments ThreadSleep {code obj}.
Arguments AbNew {code obj} b.
Arguments AbGet {code obj} r.
Arguments AbSet {code obj} r b.
Arguments AbGetAndSet {code obj} r b.
Arguments AiNew {code obj} z.
Arguments AiIncrementAndGet {code obj} r.
Arguments AiDecrementAndGet {code obj} r.
Arguments CfNew {code obj}.
Arguments CfComplete {code obj} r v.
Arguments CfCompleteExceptionally {code obj} r e.
Arguments CfGet {code obj} r.
Arguments CfIsCompletedExceptionally {code obj} r.
Arguments CfExceptionNow {code obj} r.
Arguments TsNew {code obj}.
Arguments TsAdd {code obj} r u.
Arguments TsRemove {code obj} r u.
Arguments TsContains {code obj} r u.
Arguments TsIsEmpty {code obj} r.
Arguments TsNext {code obj} r seen.
Arguments EsNew {code obj}.
Arguments EsAdd {code obj} r e.
Arguments EsNext {code obj} r seen.
Arguments VsNew {code obj}.
Arguments VsAdd {code obj} r v.
Arguments VsNext {code obj} r seen.
Arguments ArNew {code obj} v.
Arguments ArGet {code obj} r.
Arguments ArGetAndSet {code obj} r v.
Arguments ArUpdateAndGet {code obj} r f.
Arguments TlGet {code obj} r.
Arguments TlSet {code obj} r v.
Arguments AddSuppressed {code obj} e e'.
Arguments Extern {code obj} X name.
Arguments TypeError {code obj} X.
Arguments Chaos {code obj} X what.
Arguments ThreadInterrupted {code obj}.
Arguments ThreadYield {code obj}.
Arguments Park {code obj}.
Arguments NanoTime {code obj}.
Arguments SemNew {code obj} permits.
Arguments SemAcquire {code obj} r.
Arguments SemRelease {code obj} r.
Arguments BqNew {code obj} capacity.
Arguments BqPut {code obj} r v.
Arguments BqTake {code obj} r.
Arguments ObjNew {code obj} cls fields.
Arguments ObjGet {code obj} r name.
Arguments ObjSet {code obj} r name v.
Arguments ObjClass {code obj} r.
Arguments ArCas {code obj} r expected new.
Arguments VUnit {code obj}.
Arguments VBool {code obj} b.
Arguments VTid {code obj} t.
Arguments VExn {code obj} e.
Arguments VObj {code obj} o.
Arguments VCode {code obj} c.
Arguments VList {code obj} vs.
Arguments VAny {code obj} n.
