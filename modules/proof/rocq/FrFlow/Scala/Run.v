(** Running a program: the meaning of its trees, executed.

    The contracts of `FrFlow.Threads.Jdk` say what a call may do; here each is given one thing it does, so that
    a program can be run: a new object takes the next free number, a blocking call waits until it can return, a
    traversal gives the elements in order. Threads take turns, one step each. A run is one of the runs the
    contracts allow, chosen; it is what the meaning is tested with, against what the same program gives on the
    JVM. It proves nothing of the other runs. *)

From Stdlib Require Import String List ZArith NArith Bool.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem.
Require FrFlow.Threads.Lang.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition jst : Type := Jdk.jst code obj.
Definition op : Type -> Type := Jdk.op code obj.

(** What the run keeps beside the JDK's state: the next free number (of a thread, of an object), and for
    `compareAndSet` how often each reference was written and what each thread last saw of it. *)
Record extra := Extra {
  x_next : nat;
  x_written : list (nat * nat);
  x_seen : list (tid * nat * nat) }.

Definition written (x : extra) (r : nat) : nat :=
  match find (fun p => Nat.eqb (fst p) r) (x_written x) with Some p => snd p | None => 0 end.
Definition wrote (x : extra) (r : nat) : extra :=
  Extra (x_next x) ((r, S (written x r)) :: x_written x) (x_seen x).
Definition saw (x : extra) (t : tid) (r : nat) : extra :=
  Extra (x_next x) (x_written x) ((t, r, written x r) :: x_seen x).
Definition seen (x : extra) (t : tid) (r : nat) : option nat :=
  match find (fun p => Nat.eqb (fst (fst p)) t && Nat.eqb (snd (fst p)) r) (x_seen x) with
  | Some p => Some (snd p)
  | None => None
  end.
Definition took (x : extra) : extra := Extra (S (x_next x)) (x_written x) (x_seen x).

(** What a call does in this run: it returns, or it waits, or it has no meaning to run. A call that starts a
    thread says which. *)
Inductive answer (X : Type) : Type :=
  | Did (x : X) (σ : jst) (e : extra) (started : option tid)
  | Waits
  | Cannot (why : string).
Arguments Did {X} x σ e started.
Arguments Waits {X}.
Arguments Cannot {X} why.

Definition did {X : Type} (x : X) (σ : jst) (e : extra) : answer X := Did x σ e None.

(** A blocking call: its result once it can return, the interrupt if the caller is interrupted, else it waits. *)
Definition blocking {X : Type} (t : tid) (σ : jst) (e : extra) (ready : option (X * jst)) : answer (exn + X) :=
  match ready with
  | Some (x, σ') => did (inr x) σ' e
  | None => if interrupted σ t then did (inl InterruptedException) (clear_intr σ t) e else Waits
  end.

Definition fresh {X A : Type} (slot : option A) (e : extra) (make : nat -> answer X) : answer X :=
  match slot with
  | None => make (x_next e)
  | Some _ => Cannot "the next free number is taken"
  end.

Fixpoint first_not {A : Type} (eqb : A -> A -> bool) (xs seen : list A) : option A :=
  match xs with
  | [] => None
  | x :: rest => if existsb (eqb x) seen then first_not eqb rest seen else Some x
  end.

Definition oprun (t : tid) (X : Type) (o : op X) : jst -> extra -> answer X :=
  match o in Jdk.op _ _ X return jst -> extra -> answer X with
  | CurrentThread => fun σ e => did (inr t) σ e
  | NewThread c => fun σ e => fresh (j_th σ (x_next e)) e (fun u =>
      did (inr u) (set_th σ u (Thread c TNew false)) (took e))
  | ThreadStart u => fun σ e =>
      match j_th σ u with
      | Some (Thread c TNew i) => Did (inr tt) (set_th σ u (Thread c TStarted i)) e (Some u)
      | _ => did (inl IllegalThreadStateException) σ e
      end
  | ThreadInterrupt u => fun σ e =>
      match j_th σ u with
      | Some (Thread c TTerminated i) => did (inr tt) σ e
      | Some (Thread c s i) => did (inr tt) (set_th σ u (Thread c s true)) e
      | None => did (inr tt) σ e
      end
  | ThreadJoin u => fun σ e =>
      if interrupted σ t then did (inl InterruptedException) (clear_intr σ t) e else
      match j_th σ u with
      | Some (Thread _ TStarted _) => Waits
      | _ => did (inr tt) σ e
      end
  | ThreadSleep => fun σ e =>
      if interrupted σ t then did (inl InterruptedException) (clear_intr σ t) e else did (inr tt) σ e
  | AbNew b => fun σ e => fresh (j_ab σ (x_next e)) e (fun r => did (inr r) (set_ab σ r b) (took e))
  | AbGet r => fun σ e => match j_ab σ r with Some b => did (inr b) σ e | None => Cannot "no such AtomicBoolean" end
  | AbSet r b => fun σ e =>
      match j_ab σ r with Some _ => did (inr tt) (set_ab σ r b) e | None => Cannot "no such AtomicBoolean" end
  | AbGetAndSet r b => fun σ e =>
      match j_ab σ r with Some b0 => did (inr b0) (set_ab σ r b) e | None => Cannot "no such AtomicBoolean" end
  | AiNew z => fun σ e => fresh (j_ai σ (x_next e)) e (fun r => did (inr r) (set_ai σ r z) (took e))
  | AiIncrementAndGet r => fun σ e =>
      match j_ai σ r with
      | Some z => did (inr (z + 1)%Z) (set_ai σ r (z + 1)%Z) e
      | None => Cannot "no such AtomicInteger"
      end
  | AiDecrementAndGet r => fun σ e =>
      match j_ai σ r with
      | Some z => did (inr (z - 1)%Z) (set_ai σ r (z - 1)%Z) e
      | None => Cannot "no such AtomicInteger"
      end
  | CfNew => fun σ e => fresh (j_cf σ (x_next e)) e (fun r => did (inr r) (set_cf σ r None) (took e))
  | CfComplete r v => fun σ e =>
      match j_cf σ r with
      | Some None => did (inr true) (set_cf σ r (Some (inr v))) e
      | Some (Some _) => did (inr false) σ e
      | None => Cannot "no such CompletableFuture"
      end
  | CfCompleteExceptionally r x => fun σ e =>
      match j_cf σ r with
      | Some None => did (inr true) (set_cf σ r (Some (inl x))) e
      | Some (Some _) => did (inr false) σ e
      | None => Cannot "no such CompletableFuture"
      end
  | CfGet r => fun σ e =>
      match j_cf σ r with
      | Some (Some (inr v)) => did (inr v) σ e
      | Some (Some (inl x)) => did (inl (ExecutionException x)) σ e
      | Some None => blocking t σ e None
      | None => Cannot "no such CompletableFuture"
      end
  | CfIsCompletedExceptionally r => fun σ e =>
      match j_cf σ r with
      | Some (Some (inl _)) => did (inr true) σ e
      | Some _ => did (inr false) σ e
      | None => Cannot "no such CompletableFuture"
      end
  | CfExceptionNow r => fun σ e =>
      match j_cf σ r with
      | Some (Some (inl x)) => did (inr x) σ e
      | Some _ => did (inl IllegalStateException) σ e
      | None => Cannot "no such CompletableFuture"
      end
  | TsNew => fun σ e => fresh (j_ts σ (x_next e)) e (fun r => did (inr r) (set_ts σ r (fun _ => false)) (took e))
  | TsAdd r u => fun σ e =>
      match j_ts σ r with
      | Some s => did (inr (negb (s u))) (set_ts σ r (upd s u true)) e
      | None => Cannot "no such set"
      end
  | TsRemove r u => fun σ e =>
      match j_ts σ r with
      | Some s => did (inr (s u)) (set_ts σ r (upd s u false)) e
      | None => Cannot "no such set"
      end
  | TsContains r u => fun σ e =>
      match j_ts σ r with Some s => did (inr (s u)) σ e | None => Cannot "no such set" end
  | TsIsEmpty r => fun σ e =>
      match j_ts σ r with
      | Some s => did (inr (forallb (fun u => negb (s u)) (seq 0 (x_next e)))) σ e
      | None => Cannot "no such set"
      end
  | TsNext r done => fun σ e =>
      match j_ts σ r with
      | Some s => did (inr (first_not Nat.eqb (filter s (seq 0 (x_next e))) done)) σ e
      | None => Cannot "no such set"
      end
  | EsNew => fun σ e => fresh (j_es σ (x_next e)) e (fun r => did (inr r) (set_es σ r []) (took e))
  | EsAdd r x => fun σ e =>
      match j_es σ r with
      | Some s => did (inr (negb (existsb (FrFlow.Threads.Lang.exn_eqb x) s))) (set_es σ r (x :: s)) e
      | None => Cannot "no such set"
      end
  | EsNext r done => fun σ e =>
      match j_es σ r with
      | Some s => did (inr (first_not FrFlow.Threads.Lang.exn_eqb (rev s) done)) σ e
      | None => Cannot "no such set"
      end
  | VsNew => fun σ e => fresh (j_vs σ (x_next e)) e (fun r => did (inr r) (set_vs σ r []) (took e))
  | VsAdd r v => fun σ e =>
      match j_vs σ r with Some s => did (inr true) (set_vs σ r (v :: s)) e | None => Cannot "no such set" end
  | VsNext r done => fun σ e =>
      match j_vs σ r with
      | Some s => did (inr (nth_error (rev s) (List.length done))) σ e
      | None => Cannot "no such set"
      end
  | ArNew v => fun σ e => fresh (j_ar σ (x_next e)) e (fun r => did (inr r) (set_ar σ r v) (took e))
  | ArGet r => fun σ e =>
      match j_ar σ r with Some v => did (inr v) σ (saw e t r) | None => Cannot "no such AtomicReference" end
  | ArGetAndSet r v => fun σ e =>
      match j_ar σ r with
      | Some v0 => did (inr v0) (set_ar σ r v) (wrote e r)
      | None => Cannot "no such AtomicReference"
      end
  | ArUpdateAndGet r f => fun σ e =>
      match j_ar σ r with
      | Some v0 => match f v0 with
          | inr v1 => did (inr v1) (set_ar σ r v1) (wrote e r)
          | inl x => did (inl x) σ e
          end
      | None => Cannot "no such AtomicReference"
      end
  | ArCas r expected new => fun σ e =>
      match j_ar σ r with
      | Some _ =>
          if match seen e t r with Some n => Nat.eqb n (written e r) | None => false end
          then did (inr true) (set_ar σ r new) (wrote e r)
          else did (inr false) σ e
      | None => Cannot "no such AtomicReference"
      end
  | TlGet r => fun σ e => did (inr (j_tl σ r t)) σ e
  | TlSet r v => fun σ e => did (inr tt) (set_tl σ r t v) e
  | AddSuppressed _ _ => fun σ e => did (inr tt) σ e
  | Extern _ name => fun σ e => Cannot (cat "code that is not read: " name)
  | TypeError _ => fun σ e => Cannot "a cast that failed"
  | Chaos _ what => fun σ e => Cannot what
  | ThreadInterrupted => fun σ e => did (inr (interrupted σ t)) (clear_intr σ t) e
  | ThreadYield => fun σ e => did (inr tt) σ e
  | Park => fun σ e => did (inr tt) σ e
  | NanoTime => fun σ e => did (inr 0%Z) σ e
  | SemNew n => fun σ e => fresh (j_sem σ (x_next e)) e (fun r => did (inr r) (set_sem σ r n) (took e))
  | SemAcquire r => fun σ e =>
      match j_sem σ r with
      | Some (S n) => did (inr tt) (set_sem σ r n) e
      | Some 0 => blocking t σ e None
      | None => Cannot "no such Semaphore"
      end
  | SemRelease r => fun σ e =>
      match j_sem σ r with Some n => did (inr tt) (set_sem σ r (S n)) e | None => Cannot "no such Semaphore" end
  | BqNew c => fun σ e => fresh (j_bq σ (x_next e)) e (fun r => did (inr r) (set_bq σ r (c, [])) (took e))
  | BqPut r v => fun σ e =>
      match j_bq σ r with
      | Some (c, q) =>
          blocking t σ e (if Nat.ltb (List.length q) c then Some (tt, set_bq σ r (c, q ++ [v])) else None)
      | None => Cannot "no such queue"
      end
  | BqTake r => fun σ e =>
      match j_bq σ r with
      | Some (c, v :: q) => did (inr v) (set_bq σ r (c, q)) e
      | Some (c, []) => blocking t σ e None
      | None => Cannot "no such queue"
      end
  | ObjNew cls fields => fun σ e =>
      fresh (j_obj σ (x_next e)) e (fun r => did (inr r) (set_obj σ r (cls, fields)) (took e))
  | ObjGet r name => fun σ e =>
      match j_obj σ r with
      | Some (cls, fields) => match field fields name with
          | Some v => did (inr v) σ e
          | None => Cannot (cat "a field read before it is given a value: " name)
          end
      | None => Cannot "no such object"
      end
  | ObjSet r name v => fun σ e =>
      match j_obj σ r with
      | Some (cls, fields) => did (inr tt) (set_obj σ r (cls, with_field fields name v)) e
      | None => Cannot "no such object"
      end
  | ObjClass r => fun σ e =>
      match j_obj σ r with Some (cls, _) => did (inr cls) σ e | None => Cannot "no such object" end
  | LazyEnter r name monitor => fun σ e =>
      match j_obj σ r with
      | Some (cls, fields) =>
          match field fields name, holder fields name with
          | Some v, _ => did (inr (Some v)) σ e
          | None, None => did (inr None) (set_obj σ r (cls, with_field fields (evaluating name) (VTid t))) e
          | None, Some u =>
              if monitor then (if Nat.eqb u t then did (inr None) σ e else Waits)
              else blocking t σ e None
          end
      | None => Cannot "no such object"
      end
  end.

Arguments oprun t {X} o.

(** ** Threads in turn *)

Definition P : Type -> Type := Sem.P code obj.
Definition res : Type := Sem.res code obj.

Record world := World {
  w_st : jst;
  w_pool : list (tid * P res);
  w_extra : extra;
  w_ended : list (tid * res) }.

(** How a run ends: every thread has ended (with what each gave); or those left all wait; or a step has no
    meaning to run; or the run was cut short. *)
Inductive verdict :=
  | Finished (ended : list (tid * res)) (steps : nat)
  | Deadlock (waiting : list tid) (ended : list (tid * res)) (steps : nat)
  | Stopped (why : string) (thread : tid) (steps : nat)
  | Unfinished (ended : list (tid * res)).

Section Run.

  Variable interp : code -> val -> P res.

  Definition set_pool (pool : list (tid * P res)) (t : tid) (p : P res) : list (tid * P res) :=
    map (fun entry => if Nat.eqb (fst entry) t then (t, p) else entry) pool.

  (** One step of thread `t`, whose program is `p`: the world after it, or that the thread waits, or why it
      cannot be run. *)
  Definition step (w : world) (t : tid) (p : P res) : world + (unit + string) :=
    match p with
    | Ret r =>
        inl (World (terminate (w_st w) t) (filter (fun entry => negb (Nat.eqb (fst entry) t)) (w_pool w))
          (w_extra w) (w_ended w ++ [(t, r)]))
    | Vis o k =>
        match oprun t o (w_st w) (w_extra w) with
        | Did x σ e started =>
            let pool := set_pool (w_pool w) t (k x) in
            let pool' := match started with
              | Some u => match j_th σ u with
                  | Some th => pool ++ [(u, interp (t_code th) VUnit)]
                  | None => pool
                  end
              | None => pool
              end in
            inl (World σ pool' e (w_ended w))
        | Waits => inr (inl tt)
        | Cannot why => inr (inr why)
        end
    | Iter body s k => inl (World (w_st w) (set_pool (w_pool w) t (unfold_iter body s k)) (w_extra w) (w_ended w))
    | Call c arg k => inl (World (w_st w) (set_pool (w_pool w) t (pbind (interp c arg) k)) (w_extra w) (w_ended w))
    end.

  (** Which thread a turn tries first: its place among those that have not ended, taken modulo how many. *)
  Variable order : nat -> nat.

  (** A step of some thread at each turn: the one `order` names, or, if it waits, the next that does not;
      `idle` is how many have waited this turn. *)
  Fixpoint run (fuel : nat) (w : world) (turn idle steps : nat) : verdict :=
    match fuel with
    | 0 => Unfinished (w_ended w)
    | S fuel' =>
        match w_pool w with
        | [] => Finished (w_ended w) steps
        | pool =>
            let n := List.length pool in
            if Nat.leb n idle then Deadlock (map fst pool) (w_ended w) steps else
            match nth_error pool (Nat.modulo (order turn + idle) n) with
            | Some (t, p) =>
                match step w t p with
                | inl w' => run fuel' w' (S turn) 0 (S steps)
                | inr (inl _) => run fuel' w turn (S idle) steps
                | inr (inr why) => Stopped why t steps
                end
            | None => Unfinished (w_ended w)
            end
        end
    end.

End Run.

(** ** A program, started

    A module with values of its own is an object at a fixed place (`Table.module_at`). The first thread
    initialises those the program may use (`needed`), in the order the program declares them, then calls `main`
    on its module. The JVM initialises a module when it is first used: the two differ only where an initialiser
    does more than make objects. *)

Definition first : tid := 0.

(** The modules with state that `main` may reach. *)
Definition needed (T : table) (files : list tree) (from : list sym) : list string :=
  let reached := owners (fst (reaches "" files from)) in
  filter (fun m => existsb (String.eqb m) reached) (stateful_modules T).

Section Start.

  Variable T : table.
  Variable outside : string -> string -> option primitive.
  Variable supers : string -> list string.

  Definition state0 (c : code) : jst :=
    Jst (fun u => if Nat.eqb u first then Some (Thread c TStarted false) else None)
        (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None)
        (fun _ => None) (fun _ _ => None) (fun _ => None) (fun _ => None)
        (fun r => match r with
           | 0 => None
           | S i => match nth_error (stateful_modules T) i with Some cls => Some (cls, []) | None => None end
           end).

  (** What the first thread runs. *)
  Definition program (modules : list string) (main : sym) : P res :=
    let owner := match main with Member o _ _ => o | _ => "" end in
    leave "" (
      _ <~ oeach (fun cls => ocall (Init cls) (VList [module_val T cls])) modules ;;
      ocall (Method main) (VList [module_val T owner])).

  Definition world0 (modules : list string) (main : sym) : world :=
    World (state0 (Method main)) [(first, program modules main)]
      (Extra (S (List.length (stateful_modules T))) [] []) [].

  (** The program run from `main`, for at most `fuel` steps, the threads taking turns as `order` says. *)
  Definition execute_under (order : nat -> nat) (fuel : nat) (modules : list string) (main : sym) : verdict :=
    run (interp T outside supers) order fuel (world0 modules main) 0 0 0.

  (** Each thread in turn. *)
  Definition execute : nat -> list string -> sym -> verdict := execute_under (fun turn => turn).

  (** What the first thread gave, where every thread ended. *)
  Definition result (v : verdict) : option res :=
    match v with
    | Finished ended _ => match find (fun entry => Nat.eqb (fst entry) first) ended with
        | Some entry => Some (snd entry)
        | None => None
        end
    | _ => None
    end.

End Start.

(** An order of turns that follows no pattern of the program's: a sequence fixed by `seed`. Every thread that
    can step gets a turn again and again, so a loop that waits for another thread is not run for ever. *)
Definition shuffled (seed : nat) (turn : nat) : nat :=
  let x := (N.of_nat turn * 2654435761 + N.of_nat seed * 40503 + 12345)%N in
  N.to_nat (N.modulo (N.div x 65536) 1021).
