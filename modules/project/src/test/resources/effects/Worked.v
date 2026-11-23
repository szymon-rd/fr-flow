(** Worked examples for `docs/EFFECT-TREES.md`: each claim the document makes of a small program is proven here.

    1. One definition, `bump`, alone and in two threads of the JVM: it adds one; an update is lost without the
       monitor; both are counted with it.
    2. cats-effect: a claim proven from three assumed laws alone.
    3. One layer down: what the first of those laws says of outcomes is a theorem of the interleaving; code it
       does not cover.
    4. "Does the same" as what the laws derive.
    5. A value that is run later (`IO`), a lambda as a value: what running does follows from statements.
    6. A program over two vocabularies; an operation that takes a program of its own vocabulary. *)

From Stdlib Require Import Lia.
From FrFlow.Effect Require Import Tree.

Notation "x <~ e ;; k" := (Vis e (fun x => k)) (at level 61, e at next level, right associativity).

(** * Two programs whose operations interleave. Nothing here says what an operation is. *)

Inductive many {C : Type} (step : C -> C -> Prop) : C -> C -> Prop :=
  | many_none c : many step c c
  | many_more c c' c'' : step c c' -> many step c' c'' -> many step c c''.

Lemma kept {C : Type} (step : C -> C -> Prop) (I : C -> Prop) :
  (forall c c', I c -> step c c' -> I c') -> forall c c', many step c c' -> I c -> I c'.
Proof. intros Hstep c c' Hmany. induction Hmany; intros HI; [ exact HI | apply IHHmany; eauto ]. Qed.

Section Pool.
  Variable E : Type -> Type.
  Variable St : Type.
  (** What an operation does, done by one of the two threads: given by the vocabulary's statements. *)
  Variable does : bool -> forall X : Type, E X -> St -> X -> St -> Prop.

  (** One thread does its next operation. *)
  Definition moves {A : Type} (who : bool) (t : tree E A) (s : St) (t' : tree E A) (s' : St) : Prop :=
    match t with
    | Vis e k => exists x, does who _ e s x s' /\ t' = k x
    | _ => False
    end.

  Definition step {A B : Type} (c c' : tree E A * tree E B * St) : Prop :=
    let '(a, b, s) := c in
    let '(a', b', s') := c' in
    (moves false a s a' s' /\ b' = b) \/ (moves true b s b' s' /\ a' = a).

  (** Both ran to their end, in some order of their operations. *)
  Definition ends {A B : Type} (a : tree E A) (b : tree E B) (s : St) (x : A) (y : B) (s' : St) : Prop :=
    many step (a, b, s) (Ret x, Ret y, s').
End Pool.

Arguments ends {E St} does {A B} a b s x y s'.
Arguments step {E St} does {A B} c c'.

(** Two vocabularies together: an operation of one or of the other. *)
Inductive sum1 (E F : Type -> Type) (X : Type) : Type :=
  | inl1 (e : E X)
  | inr1 (f : F X).
Arguments inl1 {E F X} e.
Arguments inr1 {E F X} f.

(** * 1. Threads of the JVM: a number in memory, and a monitor *)

(** Memory, here one number: it is read, it is written. *)
Inductive mem : Type -> Type :=
  | Get : mem nat
  | Put (v : nat) : mem unit.

(** What is assumed of memory: a read gives what is there, a write leaves what was written. It is the meaning
    of a field that is `volatile` or accessed without a data race; of a plain field that threads race on, the
    JVM allows more (JLS 17.4). *)
Definition stores (X : Type) (e : mem X) (n : nat) : X -> nat -> Prop :=
  match e in mem X return X -> nat -> Prop with
  | Get => fun x n' => x = n /\ n' = n
  | Put v => fun _ n' => n' = v
  end.

(** `count = count + 1`: over memory alone. Nothing in it speaks of threads or of a monitor. *)
Definition bump : tree mem unit := x <~ Get ;; _ <~ Put (S x) ;; Ret tt.

(** Claim: run by one thread alone, it adds one. *)
Definition alone {A : Type} (c c' : tree mem A * nat) : Prop :=
  moves mem nat (fun _ => stores) false (fst c) (snd c) (fst c') (snd c').

Lemma bump_alone_adds_one n : many alone (bump, n) (Ret tt, S n).
Proof.
  apply many_more with (c' := (_ <~ Put (S n) ;; Ret tt, n)). { exists n. cbn. auto. }
  apply many_more with (c' := (Ret tt, S n)). { exists tt. cbn. auto. }
  apply many_none.
Qed.

(** Claim: two threads that run it at once can lose one: both end, and the number is 1. *)
Lemma bump_loses_one : ends (fun _ => stores) bump bump 0 tt tt 1.
Proof.
  unfold ends, bump.
  apply many_more with (c' := (_ <~ Put 1 ;; Ret tt, bump, 0)).
  { left. cbn. split; [ exists 0; auto | reflexivity ]. }
  apply many_more with (c' := (_ <~ Put 1 ;; Ret tt, _ <~ Put 1 ;; Ret tt, 0)).
  { right. cbn. split; [ exists 0; auto | reflexivity ]. }
  apply many_more with (c' := (Ret tt, _ <~ Put 1 ;; Ret tt, 1)).
  { left. cbn. split; [ exists tt; auto | reflexivity ]. }
  apply many_more with (c' := (Ret tt, Ret tt, 1)).
  { right. cbn. split; [ exists tt; auto | reflexivity ]. }
  apply many_none.
Qed.

(** A monitor, a vocabulary of its own. *)
Inductive monitor : Type -> Type :=
  | Lock : monitor unit
  | Unlock : monitor unit.

(** What is assumed of it: it is entered only when no thread holds it, and left only by the thread that holds
    it. (The JVM's can be entered again by its holder; the code here never does, and this law does not let it.) *)
Definition guards (who : bool) (X : Type) (e : monitor X) (h : option bool) : X -> option bool -> Prop :=
  match e in monitor X return X -> option bool -> Prop with
  | Lock => fun _ h' => h = None /\ h' = Some who
  | Unlock => fun _ h' => h = Some who /\ h' = None
  end.

(** The two together: each operation does what its own vocabulary says, and leaves the other's state. *)
Definition memory : Type := (nat * option bool)%type.

Definition jvm (who : bool) (X : Type) (e : sum1 monitor mem X) (s : memory) (x : X) (s' : memory) : Prop :=
  match e with
  | inl1 m => guards who X m (snd s) x (snd s') /\ fst s' = fst s
  | inr1 m => stores X m (fst s) x (fst s') /\ snd s' = snd s
  end.

(** A program over memory, as one over memory and a monitor: the same operations. *)
Fixpoint within {A : Type} (t : tree mem A) : tree (sum1 monitor mem) A :=
  match t with
  | Ret a => Ret a
  | Vis e k => Vis (inr1 e) (fun x => within (k x))
  | Iter body s k => Iter (fun s => within (body s)) s (fun b => within (k b))
  end.

(** `synchronized { count = count + 1 }`: `bump`, the definition above, between entering and leaving. *)
Definition guarded : tree (sum1 monitor mem) unit :=
  _ <~ inl1 Lock ;; bind (within bump) (fun _ => _ <~ inl1 Unlock ;; Ret tt).

(** Where a thread is in `guarded`, and what it has added so far: before the monitor, holding it, holding it
    having read the number, holding it having written, done. *)
Definition g1 : tree (sum1 monitor mem) unit :=
  x <~ inr1 Get ;; _ <~ inr1 (Put (S x)) ;; _ <~ inl1 Unlock ;; Ret tt.
Definition g2 (x : nat) : tree (sum1 monitor mem) unit := _ <~ inr1 (Put (S x)) ;; _ <~ inl1 Unlock ;; Ret tt.
Definition g3 : tree (sum1 monitor mem) unit := _ <~ inl1 Unlock ;; Ret tt.

Inductive at_ (who : bool) : tree (sum1 monitor mem) unit -> memory -> nat -> Prop :=
  | at_start n h : h <> Some who -> at_ who guarded (n, h) 0
  | at_held n : at_ who g1 (n, Some who) 0
  | at_read n : at_ who (g2 n) (n, Some who) 0
  | at_wrote n : at_ who g3 (n, Some who) 1
  | at_done n h : h <> Some who -> at_ who (Ret tt) (n, h) 1.

(** What holds at every moment: the number is what the two threads have added. *)
Definition counted (c : tree (sum1 monitor mem) unit * tree (sum1 monitor mem) unit * memory) : Prop :=
  let '(a, b, s) := c in exists i j, at_ false a s i /\ at_ true b s j /\ fst s = i + j.

Ltac there := first
  [ apply at_start; congruence | apply at_held | apply at_read | apply at_wrote | apply at_done; congruence ].

Ltac both := unfold counted; do 2 eexists; (split; [| split ]); [ there | there | cbn in *; lia ].

(** One thread (`Hmover`) does its next operation; the other (`Hother`) stays where it is. *)
Ltac moved Hmove Hmover Hother :=
  inversion Hmover; subst; cbn in Hmove; try contradiction;
  destruct Hmove as (? & Hdoes & ->); cbn in Hdoes;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; subst;
  inversion Hother; subst; try congruence; both.

Lemma counted_kept c c' : counted c -> step jvm c c' -> counted c'.
Proof.
  destruct c as [[a b] [n h]], c' as [[a' b'] [n' h']]. intros (i & j & Ha & Hb & Hn) Hstep. cbn in Hn.
  destruct Hstep as [[Hmove ->] | [Hmove ->]]; [ moved Hmove Ha Hb | moved Hmove Hb Ha ].
Qed.

(** Claim: two threads that bump holding the monitor always count both: however their operations interleave,
    when both have ended the number is 2 and no thread holds the monitor. *)
Theorem guarded_counts_both x y s' : ends jvm guarded guarded (0, None) x y s' -> s' = (2, None).
Proof.
  intros Hends. apply (kept _ counted counted_kept) in Hends.
  - destruct s' as [n h]. destruct Hends as (i & j & Ha & Hb & Hn).
    inversion Ha; subst; inversion Hb; subst. cbn in Hn. subst n. destruct h as [[] |]; congruence.
  - exists 0, 0. repeat split; apply at_start; discriminate.
Qed.

(** * 2. cats-effect: a `Ref`, and two computations run together. No thread, no object, no monitor. *)

Inductive cell : Type -> Type :=
  | Update (f : nat -> nat) : cell unit
  | Read : cell nat.

Inductive cats : Type -> Type :=
  | Do {X : Type} (e : cell X) : cats X
  | Par {X Y : Type} (a : tree cell X) (b : tree cell Y) : cats (X * Y).

Definition update (f : nat -> nat) : tree cats unit := _ <~ Do (Update f) ;; Ret tt.
Definition read : tree cats nat := x <~ Do Read ;; Ret x.
Definition par {X Y : Type} (a : tree cell X) (b : tree cell Y) : tree cats (X * Y) := r <~ Par a b ;; Ret r.
(** `ref.update(f)`, as what one of the two computations run together does. *)
Definition updating (f : nat -> nat) : tree cell unit := _ <~ Update f ;; Ret tt.

Section FromTheLaws.
  (** "Does the same", and what is assumed of it: it is transitive and kept by what follows. *)
  Variable same : forall A : Type, tree cats A -> tree cats A -> Prop.
  Notation "t ~~ u" := (same _ t u) (at level 70).
  Hypothesis same_then : forall (A : Type) (t u v : tree cats A), t ~~ u -> u ~~ v -> t ~~ v.
  Hypothesis same_before : forall (A B : Type) (t u : tree cats A) (k : A -> tree cats B),
    t ~~ u -> bind t k ~~ bind u k.

  (** What is assumed of cats-effect, of a `Ref` that nothing else running alongside touches (here the program
      is the only one that has it).
      - `update` is one step, so two updates run together are one after the other, in some order; when the two
        functions commute the order does not matter.
      - Two updates in a row are one update.
      - Reading after an update is updating after reading, the function applied to what was read.
      Next to other code that touches the `Ref`, the last two do not hold: it could run in between. *)
  Hypothesis par_updates : forall f g : nat -> nat, (forall n, f (g n) = g (f n)) ->
    par (updating f) (updating g) ~~ bind (update f) (fun _ => bind (update g) (fun _ => Ret (tt, tt))).
  Hypothesis update_update : forall (A : Type) (f g : nat -> nat) (k : unit -> tree cats A),
    bind (update f) (fun _ => bind (update g) k) ~~ bind (update (fun n => g (f n))) k.
  Hypothesis update_read : forall (A : Type) (f : nat -> nat) (k : nat -> tree cats A),
    bind (update f) (fun _ => bind read k) ~~ bind read (fun x => bind (update f) (fun _ => k (f x))).

  (** `(ref.update(_ + 1), ref.update(_ + 1)).parTupled *> ref.get` *)
  Definition both_then_read : tree cats nat := bind (par (updating S) (updating S)) (fun _ => read).

  (** Claim: it gives what the `Ref` held plus two, and leaves that in it. *)
  Theorem both_then_read_adds_two :
    both_then_read ~~ bind read (fun x => bind (update (fun n => S (S n))) (fun _ => Ret (S (S x)))).
  Proof.
    unfold both_then_read.
    eapply same_then. { apply same_before. apply par_updates. reflexivity. }
    eapply same_then. { exact (update_update _ S S (fun _ => read)). }
    exact (update_read _ (fun n => S (S n)) (fun x => Ret x)).
  Qed.
End FromTheLaws.

(** * 3. One layer down: the law about two updates is a theorem of the interleaving, and what breaks it. *)

Definition runtime (who : bool) (X : Type) (e : cell X) (s : nat) : X -> nat -> Prop :=
  match e in cell X return X -> nat -> Prop with
  | Update f => fun _ s' => s' = f s
  | Read => fun x s' => x = s /\ s' = s
  end.

(** Two updates run together leave what one after the other leaves, in one of the two orders. *)
Theorem par_updates_holds (f g : nat -> nat) (s s' : nat) (x y : unit) :
  ends runtime (updating f) (updating g) s x y s' -> s' = g (f s) \/ s' = f (g s).
Proof.
  intros Hends. inversion Hends as [| c c' c'' Hstep Hrest]; subst. destruct c' as [[a b] s1].
  destruct Hstep as [[Hmove ->] | [Hmove ->]]; cbn in Hmove; destruct Hmove as (u & -> & ->);
    inversion Hrest as [| c c' c'' Hstep' Hrest']; subst; destruct c' as [[a b] s2];
    (destruct Hstep' as [[Hmove ->] | [Hmove ->]]; cbn in Hmove; try contradiction);
    destruct Hmove as (v & -> & ->); inversion Hrest' as [| c c' c'' Hstep'' Hrest'']; subst; auto;
    destruct c' as [[a b] s3]; destruct Hstep'' as [[[] _] | [[] _]].
Qed.

(** `ref.get.flatMap(x => ref.set(x + 1))`: a read and then an update. It is not one step. *)
Definition read_then_set : tree cell unit := x <~ Read ;; _ <~ Update (fun _ => S x) ;; Ret tt.

(** Run together twice it can lose one, as the threads did: the law about two updates does not speak of it. *)
Lemma read_then_set_loses_one : ends runtime read_then_set read_then_set 0 tt tt 1.
Proof.
  unfold ends, read_then_set.
  apply many_more with (c' := (_ <~ Update (fun _ => 1) ;; Ret tt, read_then_set, 0)).
  { left. cbn. split; [ exists 0; auto | reflexivity ]. }
  apply many_more with (c' := (_ <~ Update (fun _ => 1) ;; Ret tt, _ <~ Update (fun _ => 1) ;; Ret tt, 0)).
  { right. cbn. split; [ exists 0; auto | reflexivity ]. }
  apply many_more with (c' := (Ret tt, _ <~ Update (fun _ => 1) ;; Ret tt, 1)).
  { left. cbn. split; [ exists tt; auto | reflexivity ]. }
  apply many_more with (c' := (Ret tt, Ret tt, 1)).
  { right. cbn. split; [ exists tt; auto | reflexivity ]. }
  apply many_none.
Qed.

(** * 4. "Does the same" *)

(** At the level of the laws, with no model: what the laws make equal, and nothing else. *)
Inductive same : forall A : Type, tree cats A -> tree cats A -> Prop :=
  | same_self A t : same A t t
  | same_back A t u : same A t u -> same A u t
  | same_then A t u v : same A t u -> same A u v -> same A t v
  | same_before A B t u (k : A -> tree cats B) : same A t u -> same B (bind t k) (bind u k)
  | same_after A B (t : tree cats A) (k j : A -> tree cats B) :
      (forall x, same B (k x) (j x)) -> same B (bind t k) (bind t j)
  | par_updates (f g : nat -> nat) : (forall n, f (g n) = g (f n)) ->
      same _ (par (updating f) (updating g)) (bind (update f) (fun _ => bind (update g) (fun _ => Ret (tt, tt))))
  | update_update A (f g : nat -> nat) (k : unit -> tree cats A) :
      same A (bind (update f) (fun _ => bind (update g) k)) (bind (update (fun n => g (f n))) k)
  | update_read A (f : nat -> nat) (k : nat -> tree cats A) :
      same A (bind (update f) (fun _ => bind read k)) (bind read (fun x => bind (update f) (fun _ => k (f x)))).

(** The claim of part 2 holds of this relation, with nothing assumed. *)
Theorem adds_two :
  same _ both_then_read (bind read (fun x => bind (update (fun n => S (S n))) (fun _ => Ret (S (S x))))).
Proof. exact (both_then_read_adds_two same same_then same_before par_updates update_update update_read). Qed.

(** * 5. A value that is run later, and a lambda as a value *)

Section Values.
  (** What a reference, a function value and an `IO` are is not said: each is a type of values. *)
  Variables (Ref : Type) (Fn : Type -> Type -> Type) (IO : Type -> Type).
  (** What builds an `IO` is a function on values: it does nothing. *)
  Variable io_pure : forall A : Type, A -> IO A.
  Variable io_flatMap : forall A B : Type, IO A -> Fn A (IO B) -> IO B.

  Inductive ops : Type -> Type :=
    | Load (o : Ref) : ops nat
    | Store (o : Ref) (v : nat) : ops unit
    | Apply (A B : Type) (f : Fn A B) (x : A) : ops B
    | Run (A : Type) (io : IO A) : ops A.

  Definition op {X : Type} (e : ops X) : tree ops X := Vis e (fun x => Ret x).

  Variable alike : forall A : Type, tree ops A -> tree ops A -> Prop.
  Notation "t ~~ u" := (alike _ t u) (at level 70).
  Hypothesis alike_then : forall (A : Type) (t u v : tree ops A), t ~~ u -> u ~~ v -> t ~~ v.
  Hypothesis alike_before : forall (A B : Type) (t u : tree ops A) (k : A -> tree ops B),
    t ~~ u -> bind t k ~~ bind u k.
  Hypothesis alike_after : forall (A B : Type) (t : tree ops A) (k j : A -> tree ops B),
    (forall x, k x ~~ j x) -> bind t k ~~ bind t j.

  (** What is assumed of cats-effect: running a value made by `pure` gives the value; running one made by
      `flatMap` runs the first, applies the function value to what it gave, and runs what that gave. *)
  Hypothesis run_pure : forall (A : Type) (a : A), op (Run A (io_pure A a)) ~~ Ret a.
  Hypothesis run_flatMap : forall (A B : Type) (io : IO A) (f : Fn A (IO B)),
    op (Run B (io_flatMap A B io f)) ~~
      bind (op (Run A io)) (fun x => bind (op (Apply A (IO B) f x)) (fun next => op (Run B next))).

  (** `def read(io: IO[Int]): IO[Int] = io.flatMap { x => seen = seen + 1; IO.pure(x) }`
      The lambda is a value made from the object it captures; its body is what applying it does. *)
  Variable read_1 : Ref -> Fn nat (IO nat).
  Hypothesis read_1_is : forall (this : Ref) (x : nat),
    op (Apply nat (IO nat) (read_1 this) x) ~~
      bind (op (Load this)) (fun seen => bind (op (Store this (S seen))) (fun _ => Ret (io_pure nat x))).

  (** Calling `read` builds a value and does nothing else. *)
  Definition read_ (this : Ref) (io : IO nat) : tree ops (IO nat) := Ret (io_flatMap nat nat io (read_1 this)).

  (** An `IO` that gives an `IO` is a value holding a value. *)
  Definition run_twice (io : IO (IO nat)) : tree ops nat :=
    bind (op (Run (IO nat) io)) (fun inner => op (Run nat inner)).

  (** Claim: running what `read` built runs `io`, then reads and writes `seen`, and gives what `io` gave. *)
  Theorem running_read (this : Ref) (io : IO nat) :
    op (Run nat (io_flatMap nat nat io (read_1 this))) ~~
      bind (op (Run nat io)) (fun x =>
        bind (op (Load this)) (fun seen => bind (op (Store this (S seen))) (fun _ => Ret x))).
  Proof.
    eapply alike_then; [ apply run_flatMap |]. apply alike_after. intros x.
    eapply alike_then; [ apply alike_before; apply read_1_is |]. cbn.
    refine (alike_after _ _ (op (Load this)) _ _ _). intros seen. cbn.
    refine (alike_after _ _ (op (Store this (S seen))) _ _ _). intros _. apply run_pure.
  Qed.
End Values.

(** * 6. A program over two vocabularies *)

(** A cats `Ref` read, then a field of memory read and written: each operation is of its own vocabulary. *)
Definition counting_read : tree (sum1 cell mem) nat :=
  x <~ inl1 Read ;; seen <~ inr1 Get ;; _ <~ inr1 (Put (S seen)) ;; Ret x.

(** A vocabulary whose operation takes a program of the same vocabulary: a fiber that may start fibers. *)
#[warnings="-register-all"]
Inductive fibers : Type -> Type :=
  | Start (body : tree fibers unit) : fibers nat
  | Join (fiber : nat) : fibers unit.

Definition two_deep : tree fibers unit :=
  f <~ Start (g <~ Start (Ret tt) ;; _ <~ Join g ;; Ret tt) ;; _ <~ Join f ;; Ret tt.
