(** Threads: how programs over the JDK run.

    A configuration is the JDK's state and, for each thread that has started and not ended, the program it has
    left. One step is one thread's: an operation by its contract, a turn of a loop, a call of a closure, or the
    thread's end. Any thread that can step may; no order is assumed. A thread started by a step begins with its
    closure's program. *)

From Stdlib Require Import ZArith List Bool.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk.

Set Implicit Arguments.

Section Sem.

  Variables code obj : Type.

  Definition res : Type := (exn + val code obj)%type.
  Definition P (A : Type) : Type := prog (op code obj) code (val code obj) res A.

  (** What each closure runs. *)
  Variable interp : code -> val code obj -> P res.

  Record config := Config { c_st : jst code obj; c_pool : tid -> option (P res) }.

  Definition started (σ : jst code obj) (u : tid) : Prop :=
    match j_th σ u with Some (Thread _ TStarted _) => True | _ => False end.

  Lemma started_dec σ u : started σ u \/ ~ started σ u.
  Proof. unfold started. destruct (j_th σ u) as [[c s i] |]; [destruct s |]; auto. Qed.

  (** The closure of a thread that this step started. *)
  Definition starts (σ σ' : jst code obj) (u : tid) (c : code) : Prop :=
    ~ started σ u /\ match j_th σ' u with Some (Thread c' TStarted _) => c' = c | _ => False end.

  Definition terminate (σ : jst code obj) (t : tid) : jst code obj :=
    match j_th σ t with
    | Some th => set_th σ t (Thread (t_code th) TTerminated (t_intr th))
    | None => σ
    end.

  Inductive step : config -> config -> Prop :=
    | s_op σ pl t X (o : op code obj X) k x σ' pl' :
        pl t = Some (Vis o k) -> opstep t o σ x σ' ->
        pl' t = Some (k x) ->
        (forall u, u <> t -> started σ u -> pl' u = pl u) ->
        (forall u, u <> t -> ~ started σ u -> ~ started σ' u -> pl' u = pl u) ->
        (forall u c, u <> t -> starts σ σ' u c -> pl' u = Some (interp c VUnit)) ->
        step (Config σ pl) (Config σ' pl')
    | s_iter σ pl t S B (body : S -> P (S + B)) s k :
        pl t = Some (Iter body s k) ->
        step (Config σ pl) (Config σ (upd pl t (Some (unfold_iter body s k))))
    | s_call σ pl t c arg k :
        pl t = Some (Call c arg k) ->
        step (Config σ pl) (Config σ (upd pl t (Some (pbind (interp c arg) k))))
    | s_exit σ pl t r :
        pl t = Some (Ret r) ->
        step (Config σ pl) (Config (terminate σ t) (upd pl t None)).

  Inductive steps : config -> config -> Prop :=
    | steps_refl c : steps c c
    | steps_step c c' c'' : steps c c' -> step c' c'' -> steps c c''.

End Sem.
