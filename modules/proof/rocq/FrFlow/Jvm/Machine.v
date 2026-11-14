(** The JVM as a program meets it: threads, the heap of the program's objects, and objects of classes from
    outside the program, each known by its protocol.

    A program (`FrFlow.Threads.Prog`) calls operations. An operation is one step of its thread, taken among the
    steps of other threads: that a field read or a method of a concurrent class is one step is what the memory
    model gives a program with no data race (JLS 17.4.5) and what the classes' documentation says of them.

    - **Threads** are the JVM's own: made, started once, interrupted, joined, ended. `opstep` says what each
      operation on them may do.
    - **An object of the program** is its class and its fields; a field is read and assigned. A `lazy val` and
      the initialisation of a class are entered by one thread at a time (`Enter`).
    - **An object of a class from outside** (an `AtomicBoolean`, a `CompletableFuture`) has a state only its
      methods read, and a `protocol`: for each method, from the object's state and the arguments, what the call
      gives and how it leaves the object, or that it does not return yet. A protocol is what is assumed of the
      class. It is a function, so that a program can be run (`FrFlow.Scala.Run`); where the class may do one of
      several things, the function takes a number that says which, and a step is the function at some number.
    - **Going wrong.** A program whose meaning is not known (`Chaos`), a method called as its protocol does not
      know it, a field read that the object has not: the state is marked (`s_wrong`), and nothing more is said
      of it. A proof shows the mark is never set.

    Not modelled: a thread ended from outside (`Thread.stop`), errors of the JVM itself (`OutOfMemoryError`,
    `StackOverflowError`), an exception's message, stack and suppressed exceptions. *)

From Stdlib Require Import ZArith List Bool String.
Require Import FrFlow.Threads.Prog.
Import ListNotations.

Set Implicit Arguments.
Set Warnings "-register-all".

Definition tid := nat.

(** What can be thrown: an exception of the JDK by its class, or an object of a class of the program. *)
Inductive exn :=
  | InterruptedException
  | ExecutionException (cause : exn)
  | IllegalStateException
  | IllegalThreadStateException
  | NullPointerException
  | NoSuchElementException
  | Other (class : string)
  | Thrown (r : nat).

(** What is done once, by one thread at a time: a `lazy val` of an object evaluated, one written in a method, a
    class initialised. *)
Inductive once := OfMember | OfMethod | OfClass.

Section Machine.

  (** What is the program's: the closures it makes (`code`), and its data (`obj`). *)
  Variables code obj : Type.

  Inductive val :=
    | VUnit
    | VBool (b : bool)
    | VTid (t : tid)
    | VExn (e : exn)
    | VObj (o : obj)
    | VCode (c : code)
    | VList (vs : list val).

  (** ** Threads *)

  Inductive tstatus := TNew | TStarted | TTerminated.

  (** What a thread runs, where it is in its life, its interrupt status. *)
  Record thread := Thread { t_code : code; t_status : tstatus; t_intr : bool }.

  (** ** Objects of classes from outside *)

  (** What a call of a method does. *)
  Inductive reply (S : Type) : Type :=
    | Gives (x : exn + val) (s : S)     (* it returns or throws, and leaves its object so *)
    | Waits                             (* it does not return yet; an interrupt of the caller ends the wait *)
    | Interrupted                       (* it throws InterruptedException and clears the caller's status *)
    | Unknown.                          (* the protocol has no such method, or not of such arguments *)
  Arguments Gives {S} x s.
  Arguments Waits {S}.
  Arguments Interrupted {S}.
  Arguments Unknown {S}.

  (** A class from outside: the methods known of it, the state of an object of it, what a new one is, and what a
      call of each method does
      given the caller, whether the caller is interrupted, the object's state, the arguments, and which of the
      things the class may do it does. *)
  Record protocol := Protocol {
    p_class : string;
    p_methods : list string;
    p_state : Type;
    p_new : list val -> option p_state;
    p_call : string -> tid -> bool -> p_state -> list val -> nat -> reply p_state }.

  (** An object from outside: its protocol and its state. *)
  Record held := Held { h_protocol : protocol; h_state : p_state h_protocol }.

  (** ** The state *)

  Definition object : Type := string * list (string * val).

  Record state := State {
    s_th : tid -> option thread;
    s_obj : nat -> option object;
    s_ext : nat -> option held;
    s_wrong : option string }.

  Definition upd {B : Type} (f : nat -> B) (k : nat) (v : B) : nat -> B :=
    fun x => if Nat.eq_dec x k then v else f x.

  Definition set_th σ u th := State (upd (s_th σ) u (Some th)) (s_obj σ) (s_ext σ) (s_wrong σ).
  Definition set_obj σ r o := State (s_th σ) (upd (s_obj σ) r (Some o)) (s_ext σ) (s_wrong σ).
  Definition set_ext σ r h := State (s_th σ) (s_obj σ) (upd (s_ext σ) r (Some h)) (s_wrong σ).

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

  (** Where an object keeps which thread has entered `name`. *)
  Definition entered (name : string) : string := (name ++ "<entered>")%string.
  Definition holder (fields : list (string * val)) (name : string) : option tid :=
    match field fields (entered name) with Some (VTid u) => Some u | _ => None end.

  Definition interrupted σ (t : tid) : bool :=
    match s_th σ t with Some th => t_intr th | None => false end.

  (** The caller's interrupt status cleared, as a method that throws `InterruptedException` leaves it. *)
  Definition clear_intr σ (t : tid) : state :=
    match s_th σ t with Some th => set_th σ t (Thread (t_code th) (t_status th) false) | None => σ end.

  Definition terminate σ (t : tid) : state :=
    match s_th σ t with Some th => set_th σ t (Thread (t_code th) TTerminated (t_intr th)) | None => σ end.

  Definition went_wrong (σ : state) : Prop := s_wrong σ <> None.

  (** ** The operations *)

  Inductive op : Type -> Type :=
    (* threads *)
    | CurrentThread : op (exn + tid)                         (* Thread.currentThread() *)
    | NewThread (c : code) : op (exn + tid)                  (* ThreadFactory.newThread(runnable) *)
    | ThreadStart (u : tid) : op (exn + unit)                (* thread.start() *)
    | ThreadInterrupt (u : tid) : op (exn + unit)            (* thread.interrupt() *)
    | ThreadJoin (u : tid) : op (exn + unit)                 (* thread.join() *)
    | ThreadSleep : op (exn + unit)                          (* Thread.sleep(millis) *)
    | ThreadInterrupted : op (exn + bool)                    (* Thread.interrupted() *)
    | ThreadYield : op (exn + unit)                          (* Thread.yield() *)
    | Park : op (exn + unit)                                 (* LockSupport.park() *)
    | NanoTime : op (exn + Z)                                (* System.nanoTime() *)
    (* an object of the program *)
    | ObjNew (cls : string) (fields : list (string * val)) : op (exn + nat)
    | ObjGet (r : nat) (name : string) : op (exn + val)
    | ObjSet (r : nat) (name : string) (v : val) : op (exn + unit)
    | ObjClass (r : nat) : op (exn + string)
    | Enter (r : nat) (name : string) (what : once) : op (exn + option val)
    (* an object of a class from outside *)
    | ExtNew (p : protocol) (args : list val) : op (exn + nat)
    | ExtCall (r : nat) (method : string) (args : list val) : op (exn + val)
    (* a program with no meaning *)
    | Chaos (X : Type) (what : string) : op X.

  (** What one call may do, made by thread `t` in state `σ`: its result and the state it leaves. No step: the
      call does not return yet. *)
  Definition opstep (t : tid) (X : Type) (o : op X) : state -> X -> state -> Prop :=
    match o in op X return state -> X -> state -> Prop with

    | CurrentThread => fun σ x σ' => x = inr t /\ σ' = σ

    (* A thread that did not exist, not started, not interrupted. *)
    | NewThread c => fun σ x σ' => exists u,
        s_th σ u = None /\ x = inr u /\ σ' = set_th σ u (Thread c TNew false)

    (* A thread not started starts; any other throws IllegalThreadStateException. *)
    | ThreadStart u => fun σ x σ' =>
        match s_th σ u with
        | Some (Thread c TNew i) => x = inr tt /\ σ' = set_th σ u (Thread c TStarted i)
        | _ => x = inl IllegalThreadStateException /\ σ' = σ
        end

    (* The status of a started thread is set. Of a thread not alive the documentation says it "need not have any
       effect": it is set or left. *)
    | ThreadInterrupt u => fun σ x σ' => x = inr tt /\
        match s_th σ u with
        | Some (Thread c TStarted i) => σ' = set_th σ u (Thread c TStarted true)
        | Some (Thread c s i) => σ' = set_th σ u (Thread c s true) \/ σ' = σ
        | None => σ' = σ
        end

    (* Returns once the thread is not alive (JLS 17.4.5: its actions come before the return); or the caller,
       interrupted, throws InterruptedException with its status cleared. *)
    | ThreadJoin u => fun σ x σ' =>
        (x = inr tt /\ σ' = σ /\
           match s_th σ u with Some (Thread _ TStarted _) => False | _ => True end) \/
        (x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)

    (* Returns, or the caller, interrupted, throws. Nothing is assumed of time. *)
    | ThreadSleep => fun σ x σ' =>
        (x = inr tt /\ σ' = σ) \/
        (x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t)

    (* The caller's status, cleared. *)
    | ThreadInterrupted => fun σ x σ' => x = inr (interrupted σ t) /\ σ' = clear_intr σ t

    (* A hint to the scheduler. *)
    | ThreadYield => fun σ x σ' => x = inr tt /\ σ' = σ

    (* Returns when unparked, when the caller is interrupted, or "spuriously (that is, for no reason)": it is
       taken to return at any time. *)
    | Park => fun σ x σ' => x = inr tt /\ σ' = σ

    (* Some number. *)
    | NanoTime => fun σ x σ' => exists z, x = inr z /\ σ' = σ

    (* An object of the program: a place that held none. *)
    | ObjNew cls fields => fun σ x σ' => exists r, s_obj σ r = None /\ x = inr r /\ σ' = set_obj σ r (cls, fields)
    | ObjGet r name => fun σ x σ' =>
        match s_obj σ r with
        | Some (cls, fields) => match field fields name with
            | Some v => x = inr v /\ σ' = σ
            | None => went_wrong σ'
            end
        | None => went_wrong σ'
        end
    | ObjSet r name v => fun σ x σ' =>
        match s_obj σ r with
        | Some (cls, fields) => x = inr tt /\ σ' = set_obj σ r (cls, with_field fields name v)
        | None => went_wrong σ'
        end
    | ObjClass r => fun σ x σ' =>
        match s_obj σ r with
        | Some (cls, fields) => x = inr cls /\ σ' = σ
        | None => went_wrong σ'
        end

    (* What one thread at a time evaluates: its value if it has one; else the caller is the one that evaluates
       it, if no thread is; else the caller waits. Of a member (`scala.runtime.LazyVals`) the wait is one an
       interrupt ends; of a `lazy val` written in a method (`scala.runtime.LazyRef`, a monitor) it is not, and
       the thread that holds it enters again; of a class being initialised (JLS 12.4.2) it is not, and to the
       thread that holds it the class is as good as initialised. The thread that evaluates then writes the value
       (`ObjSet`), or gives the place up. Run on the JVM in `examples/ox/probe/LazyProbe.scala`. *)
    | Enter r name what => fun σ x σ' =>
        match s_obj σ r with
        | Some (cls, fields) =>
            match field fields name, holder fields name with
            | Some v, _ => x = inr (Some v) /\ σ' = σ
            | None, None => x = inr None /\ σ' = set_obj σ r (cls, with_field fields (entered name) (VTid t))
            | None, Some u =>
                match what with
                | OfMember => x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t
                | OfMethod => u = t /\ x = inr None /\ σ' = σ
                | OfClass => u = t /\ x = inr (Some VUnit) /\ σ' = σ
                end
            end
        | None => went_wrong σ'
        end

    (* An object from outside: a place that held none, in the state its protocol gives a new one. *)
    | ExtNew p args => fun σ x σ' =>
        match p_new p args with
        | Some s => exists r, s_ext σ r = None /\ x = inr r /\ σ' = set_ext σ r (Held p s)
        | None => went_wrong σ'
        end

    (* A method of it: what its protocol says, at some one of the things the class may do. *)
    | ExtCall r method args => fun σ x σ' =>
        match s_ext σ r with
        | Some (Held p s) => exists choice,
            match p_call p method t (interrupted σ t) s args choice with
            | Gives y s' => x = y /\ σ' = set_ext σ r (Held p s')
            | Waits => x = inl InterruptedException /\ interrupted σ t = true /\ σ' = clear_intr σ t
            | Interrupted => x = inl InterruptedException /\ σ' = clear_intr σ t
            | Unknown => went_wrong σ'
            end
        | None => went_wrong σ'
        end

    | Chaos _ _ => fun σ x σ' => went_wrong σ'
    end.

  (** ** Threads' steps *)

  Definition res : Type := (exn + val)%type.
  Definition P (A : Type) : Type := prog op code val res A.

  (** What each closure runs. *)
  Variable interp : code -> val -> P res.

  (** A thread: running what is left of its program, or ended with what it gave. *)
  Inductive running :=
    | Running (t : tid) (p : P res)
    | Ended (t : tid) (r : res).

  (** The thread an operation starts. *)
  Definition forked (σ : state) (X : Type) (o : op X) : list running :=
    match o with
    | ThreadStart u =>
        match s_th σ u with
        | Some (Thread c TNew _) => [Running u (interp c VUnit)]
        | _ => []
        end
    | _ => []
    end.

  (** One step of one thread: an operation by `opstep`, a turn of a loop, a call of a closure, or its end. *)
  Definition step (e : running) (σ : state) (e' : running) (σ' : state) (started : list running) : Prop :=
    match e with
    | Ended _ _ => False
    | Running t p =>
        match p with
        | Ret r => e' = Ended t r /\ σ' = terminate σ t /\ started = []
        | Vis o k => exists x, opstep t o σ x σ' /\ e' = Running t (k x) /\ started = forked σ o
        | Iter body s k => e' = Running t (unfold_iter body s k) /\ σ' = σ /\ started = []
        | Call c arg k => e' = Running t (pbind (interp c arg) k) /\ σ' = σ /\ started = []
        end
    end.

  (** The threads there are, and the state. Any thread that can step may; no order is assumed. *)
  Definition config : Type := list running * state.

  Inductive moves : config -> config -> Prop :=
    | move before e after σ e' σ' started :
        step e σ e' σ' started ->
        moves (before ++ e :: after, σ) (before ++ e' :: after ++ started, σ').

  Inductive reaches : config -> config -> Prop :=
    | reaches_refl c : reaches c c
    | reaches_step c c' c'' : reaches c c' -> moves c' c'' -> reaches c c''.

End Machine.

Arguments VUnit {code obj}.
Arguments VBool {code obj} b.
Arguments VTid {code obj} t.
Arguments VExn {code obj} e.
Arguments VObj {code obj} o.
Arguments VCode {code obj} c.
Arguments VList {code obj} vs.
Arguments NewThread {code obj} c.
Arguments ExtNew {code obj} p args.
Arguments Gives {code obj S} x s.
Arguments Waits {code obj S}.
Arguments Interrupted {code obj S}.
Arguments Unknown {code obj S}.
Arguments CurrentThread {code obj}.
Arguments ThreadStart {code obj} u.
Arguments ThreadInterrupt {code obj} u.
Arguments ThreadJoin {code obj} u.
Arguments ThreadSleep {code obj}.
Arguments ThreadInterrupted {code obj}.
Arguments ThreadYield {code obj}.
Arguments Park {code obj}.
Arguments NanoTime {code obj}.
Arguments ObjNew {code obj} cls fields.
Arguments ObjGet {code obj} r name.
Arguments ObjSet {code obj} r name v.
Arguments ObjClass {code obj} r.
Arguments Enter {code obj} r name what.
Arguments ExtCall {code obj} r method args.
Arguments Chaos {code obj} X what.
