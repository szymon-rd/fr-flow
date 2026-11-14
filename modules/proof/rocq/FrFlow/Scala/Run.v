(** Running a program: the meaning of its trees, executed.

    The machine (`FrFlow.Jvm.Machine`) says what a step may do; here each operation is given one thing it does,
    so that a program can be run: a new object takes the next free number, a call that waits is not taken until
    it can return, a class does the first of the things its protocol lets it do. Threads take turns in an order
    given. A run is one of the runs the machine allows (`run_reaches`); it is what the meaning is tested with,
    against what the same program gives on the JVM. It proves nothing of the other runs. *)

From Stdlib Require Import String List ZArith NArith Bool Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition state : Type := Machine.state code obj.
Definition op : Type -> Type := Machine.op code obj.
Definition P : Type -> Type := Machine.P code obj.
Definition res : Type := Machine.res code obj.
Definition running : Type := Machine.running code obj.

(** What a call does in this run: it returns, or it waits, or it has no meaning to run. *)
Inductive answer (X : Type) : Type :=
  | Did (x : X) (σ : state)
  | Waits
  | Cannot (why : string).
Arguments Did {X} x σ.
Arguments Waits {X}.
Arguments Cannot {X} why.

(** A call that an interrupt ends: the interrupt if the caller is interrupted, else it waits. *)
Definition waiting {X : Type} (t : tid) (σ : state) : answer (exn + X) :=
  if interrupted σ t then Did (inl InterruptedException) (clear_intr σ t) else Waits.

(** `next` is a number no thread and no object has. *)
Definition oprun (t : tid) (next : nat) (X : Type) (o : op X) : state -> answer X :=
  match o in Machine.op _ _ X return state -> answer X with
  | CurrentThread => fun σ => Did (inr t) σ
  | NewThread c => fun σ =>
      match s_th σ next with
      | None => Did (inr next) (set_th σ next (Thread c TNew false))
      | Some _ => Cannot "the next free number is a thread's"
      end
  | ThreadStart u => fun σ =>
      match s_th σ u with
      | Some (Thread c TNew i) => Did (inr tt) (set_th σ u (Thread c TStarted i))
      | _ => Did (inl IllegalThreadStateException) σ
      end
  | ThreadInterrupt u => fun σ =>
      match s_th σ u with
      | Some (Thread c s i) => Did (inr tt) (set_th σ u (Thread c s true))
      | None => Did (inr tt) σ
      end
  | ThreadJoin u => fun σ =>
      if interrupted σ t then Did (inl InterruptedException) (clear_intr σ t) else
      match s_th σ u with
      | Some (Thread _ TStarted _) => Waits
      | _ => Did (inr tt) σ
      end
  | ThreadSleep => fun σ =>
      if interrupted σ t then Did (inl InterruptedException) (clear_intr σ t) else Did (inr tt) σ
  | ThreadInterrupted => fun σ => Did (inr (interrupted σ t)) (clear_intr σ t)
  | ThreadYield => fun σ => Did (inr tt) σ
  | Park => fun σ => Did (inr tt) σ
  | NanoTime => fun σ => Did (inr (Z.of_nat next)) σ
  | ObjNew cls fields => fun σ =>
      match s_obj σ next with
      | None => Did (inr next) (set_obj σ next (cls, fields))
      | Some _ => Cannot "the next free number is an object's"
      end
  | ObjGet r name => fun σ =>
      match s_obj σ r with
      | Some (cls, fields) => match field fields name with
          | Some v => Did (inr v) σ
          | None => Cannot (cat "a field the object has not: " name)
          end
      | None => Cannot "no such object"
      end
  | ObjSet r name v => fun σ =>
      match s_obj σ r with
      | Some (cls, fields) => Did (inr tt) (set_obj σ r (cls, with_field fields name v))
      | None => Cannot "no such object"
      end
  | ObjClass r => fun σ =>
      match s_obj σ r with Some (cls, _) => Did (inr cls) σ | None => Cannot "no such object" end
  | Enter r name what => fun σ =>
      match s_obj σ r with
      | Some (cls, fields) =>
          match field fields name, holder fields name with
          | Some v, _ => Did (inr (Some v)) σ
          | None, None => Did (inr None) (set_obj σ r (cls, with_field fields (entered name) (VTid t)))
          | None, Some u =>
              match what with
              | OfMember => waiting t σ
              | OfMethod => if Nat.eqb u t then Did (inr None) σ else Waits
              | OfClass => if Nat.eqb u t then Did (inr (Some VUnit)) σ else Waits
              end
          end
      | None => Cannot "no such object"
      end
  | ExtNew p args => fun σ =>
      match p_new p args, s_ext σ next with
      | Some s, None => Did (inr next) (set_ext σ next (Held p s))
      | Some _, Some _ => Cannot "the next free number is an object's"
      | None, _ => Cannot (cat "an object made as its class is not known to be: " (p_class p))
      end
  | ExtCall r method args => fun σ =>
      match s_ext σ r with
      | Some h =>
          match p_call (h_protocol h) method t (interrupted σ t) (h_state h) args 0 with
          | Gives y s' => Did y (set_ext σ r (Held (h_protocol h) s'))
          | Machine.Waits => waiting t σ
          | Interrupted => Did (inl InterruptedException) (clear_intr σ t)
          | Unknown => Cannot (cat "a method its class is not known to have so: "
                                 (cat (p_class (h_protocol h)) (cat "." method)))
          end
      | None => Cannot "no such object of a class from outside"
      end
  | Chaos _ why => fun σ => Cannot why
  end.

Arguments oprun t next {X} o.

(** What this run does is something the machine allows. *)
Lemma oprun_sound t next X (o : op X) σ x σ' : oprun t next o σ = Did x σ' -> opstep t o σ x σ'.
Proof.
  destruct o; cbn; intro H.
  - injection H as <- <-. auto.
  - destruct (s_th σ next) eqn:E; [discriminate |]. injection H as <- <-. eauto.
  - destruct (s_th σ u) as [[c [] i] |]; injection H as <- <-; auto.
  - destruct (s_th σ u) as [[c [] i] |]; injection H as <- <-; auto.
  - destruct (interrupted σ t) eqn:I; [injection H as <- <-; auto |].
    left. destruct (s_th σ u) as [[c [] i] |]; try discriminate; injection H as <- <-; auto.
  - destruct (interrupted σ t) eqn:I; injection H as <- <-; auto.
  - injection H as <- <-. auto.
  - injection H as <- <-. auto.
  - injection H as <- <-. auto.
  - injection H as <- <-. eauto.
  - destruct (s_obj σ next) eqn:E; [discriminate |]. injection H as <- <-. eauto.
  - destruct (s_obj σ r) as [[cls fields] |]; [| discriminate].
    destruct (field fields name); [| discriminate]. injection H as <- <-. auto.
  - destruct (s_obj σ r) as [[cls fields] |]; [| discriminate]. injection H as <- <-. auto.
  - destruct (s_obj σ r) as [[cls fields] |]; [| discriminate]. injection H as <- <-. auto.
  - destruct (s_obj σ r) as [[cls fields] |]; [| discriminate].
    destruct (field fields name); [injection H as <- <-; auto |].
    destruct (holder fields name) as [u |]; [| injection H as <- <-; auto].
    destruct what.
    + unfold waiting in H. destruct (interrupted σ t) eqn:I; [| discriminate]. injection H as <- <-. auto.
    + destruct (Nat.eqb u t) eqn:E; [| discriminate]. apply Nat.eqb_eq in E. injection H as <- <-. auto.
    + destruct (Nat.eqb u t) eqn:E; [| discriminate]. apply Nat.eqb_eq in E. injection H as <- <-. auto.
  - destruct (p_new p args); [| discriminate]. destruct (s_ext σ next) eqn:E; [discriminate |].
    injection H as <- <-. eauto.
  - destruct (s_ext σ r) as [[p s] |]; [| discriminate]. cbn in H. exists 0.
    destruct (p_call p method t (interrupted σ t) s args 0).
    + injection H as <- <-. auto.
    + unfold waiting in H. destruct (interrupted σ t) eqn:I; [| discriminate]. injection H as <- <-. auto.
    + injection H as <- <-. auto.
    + discriminate.
  - discriminate.
Qed.

(** ** Threads in turn *)

(** How a run ends: every thread has ended (with what each gave); or those left all wait; or a step has no
    meaning to run; or the run was cut short. *)
Inductive verdict :=
  | Finished (ended : list (tid * res)) (steps : nat)
  | Deadlock (waiting : list tid) (ended : list (tid * res)) (steps : nat)
  | Stopped (why : string) (thread : tid) (steps : nat)
  | Unfinished (ended : list (tid * res)).

Definition config : Type := Machine.config code obj.

Fixpoint ended_of (pool : list running) : list (tid * res) :=
  match pool with
  | [] => []
  | Ended t r :: rest => (t, r) :: ended_of rest
  | Running _ _ :: rest => ended_of rest
  end.

(** The places in the pool of the threads that have not ended, and which thread each is. *)
Fixpoint alive_from (pool : list running) (i : nat) : list (nat * tid) :=
  match pool with
  | [] => []
  | Running t _ :: rest => (i, t) :: alive_from rest (S i)
  | Ended _ _ :: rest => alive_from rest (S i)
  end.

Section Run.

  Variable interp : code -> val -> P res.

  (** One step of a thread: what it becomes, the state, and the thread it started; or that it waits; or why it
      cannot be run. *)
  Definition step_of (next : nat) (σ : state) (e : running)
      : (running * state * list running) + (unit + string) :=
    match e with
    | Ended _ _ => inr (inl tt)
    | Running t p =>
        match p with
        | Ret r => inl (Ended t r, terminate σ t, [])
        | Vis o k =>
            match oprun t next o σ with
            | Did x σ' => inl (Running t (k x), σ', forked interp σ o)
            | Waits => inr (inl tt)
            | Cannot why => inr (inr why)
            end
        | Iter body s k => inl (Running t (unfold_iter body s k), σ, [])
        | Call c arg k => inl (Running t (pbind (interp c arg) k), σ, [])
        end
    end.

  Lemma step_of_sound next σ e e' σ' started :
    step_of next σ e = inl (e', σ', started) -> Machine.step interp e σ e' σ' started.
  Proof.
    destruct e as [t p | t r]; [| discriminate]. destruct p; cbn; intro H.
    - injection H as <- <- <-. auto.
    - destruct (oprun t next o σ) eqn:E; try discriminate. injection H as <- <- <-.
      exists x. split; [eapply oprun_sound; exact E | auto].
    - injection H as <- <- <-. auto.
    - injection H as <- <- <-. auto.
  Qed.

  (** Which thread a turn tries first: its place among those that have not ended, taken modulo how many. *)
  Variable order : nat -> nat.

  (** A step of some thread at each turn: the one `order` names, or, if it waits, the next that does not;
      `idle` is how many have waited this turn. `next` is a number not yet given to a thread or an object. What
      it gives: how the run ended, and the threads and the state then. *)
  Fixpoint run (fuel : nat) (c : config) (next turn idle steps : nat) : verdict * config :=
    match fuel with
    | 0 => (Unfinished (ended_of (fst c)), c)
    | S fuel' =>
        match alive_from (fst c) 0 with
        | [] => (Finished (ended_of (fst c)) steps, c)
        | alive =>
            let n := List.length alive in
            if Nat.leb n idle then (Deadlock (map snd alive) (ended_of (fst c)) steps, c) else
            match nth_error alive (Nat.modulo (order turn + idle) n) with
            | Some (i, t) =>
                match nth_error (fst c) i with
                | Some e =>
                    match step_of next (snd c) e with
                    | inl (e', σ', started) =>
                        run fuel' (firstn i (fst c) ++ e' :: skipn (S i) (fst c) ++ started, σ')
                          (S next) (S turn) 0 (S steps)
                    | inr (inl _) => run fuel' c next turn (S idle) steps
                    | inr (inr why) => (Stopped why t steps, c)
                    end
                | None => (Unfinished (ended_of (fst c)), c)
                end
            | None => (Unfinished (ended_of (fst c)), c)
            end
        end
    end.

  Lemma reaches_first (c c' c'' : config) : Machine.moves interp c c' -> Machine.reaches interp c' c'' -> Machine.reaches interp c c''.
  Proof.
    intros M R. induction R as [| ? ? ? R IH M']; [eapply Machine.reaches_step; [constructor | exact M] |].
    eapply Machine.reaches_step; [apply IH, M | exact M'].
  Qed.

  Lemma split_at {A : Type} (xs : list A) i x : nth_error xs i = Some x -> xs = firstn i xs ++ x :: skipn (S i) xs.
  Proof.
    revert i. induction xs as [| y ys IH]; intros [| i] H; cbn in *; try discriminate.
    - injection H as <-. reflexivity.
    - f_equal. apply IH, H.
  Qed.

  (** Where a run ends is somewhere the machine's threads can get. *)
  Lemma run_reaches fuel : forall c next turn idle steps,
    Machine.reaches interp c (snd (run fuel c next turn idle steps)).
  Proof.
    induction fuel as [| fuel IH]; intros [pool σ] next turn idle steps; cbn [run fst snd]; [constructor |].
    destruct (alive_from pool 0) as [| a alive] eqn:A; [constructor |].
    match goal with |- context [if ?b then _ else _] => destruct b end; [constructor |].
    match goal with |- context [nth_error (a :: alive) ?n] => destruct (nth_error (a :: alive) n) as [[i t] |] end;
      [| constructor].
    destruct (nth_error pool i) as [e |] eqn:E; [| constructor].
    destruct (step_of next σ e) as [[[e' σ'] started] | [[] | why]] eqn:S; try constructor.
    - eapply reaches_first; [| apply IH].
      rewrite (split_at pool i e E) at 1. apply Machine.move. eapply step_of_sound. exact S.
    - apply IH.
  Qed.

End Run.

(** ** A program, started

    An object with state is at a fixed place (`Table.module_at`), there from the start with each field as the
    JVM leaves one not yet assigned; it is initialised when it is first named (`Meaning.module_obj`). The first
    thread calls `main` on its object. *)

Definition first : tid := 0.

Section Start.

  Variable T : table.
  Variable outside : string -> string -> option primitive.
  Variable supers : string -> list string.

  Definition state0 (c : code) : state :=
    State (fun u => if Nat.eqb u first then Some (Thread c TStarted false) else None)
          (fun r => match r with
             | 0 => None
             | S i => match nth_error (stateful_modules T) i with
                 | Some cls => Some (cls, fields_of T cls)
                 | None => None
                 end
             end)
          (fun _ => None) None.

  (** What the first thread runs. *)
  Definition program (main : sym) : P res :=
    let owner := match main with Member o _ _ => o | _ => "" end in
    leave "" (on <~ module_obj T owner ;; ocall (Method main) (VList [on])).

  Definition config0 (main : sym) : config := ([Running first (program main)], state0 (Method main)).

  (** The program run from `main`, for at most `fuel` steps, the threads taking turns as `order` says. *)
  Definition execute_under (order : nat -> nat) (fuel : nat) (main : sym) : verdict :=
    fst (run (interp T outside supers) order fuel (config0 main) (S (List.length (stateful_modules T))) 0 0 0).

  (** Each thread in turn. *)
  Definition execute : nat -> sym -> verdict := execute_under (fun turn => turn).

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
