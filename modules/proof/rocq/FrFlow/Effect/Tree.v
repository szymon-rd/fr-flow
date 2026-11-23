(** Programs as trees of effects.

    Code is read into a tree: it gives a value, or it does one effect and goes on with what the effect gave, or it
    loops. What is pure in the code (arithmetic, a test, a value made of values) is no node of the tree: it is a
    term of Rocq, in the value a tree gives, in what an effect is given, or in the choice of what comes next. The
    effects (`E`, each typed by what it gives) are a parameter: a tree says which are done and in what order,
    and nothing of what they do.

    A program that may throw gives an exception or a value (`prog`): `try`, `catch` and `finally` are then
    functions on trees, and a loop a throw leaves is a loop that ends. *)

Set Implicit Arguments.

Section Tree.

  Variable E : Type -> Type.

  Inductive tree (A : Type) : Type :=
    | Ret (a : A)
    | Vis (X : Type) (e : E X) (k : X -> tree A)
    | Iter (St B : Type) (body : St -> tree (St + B)) (s : St) (k : B -> tree A).

  Arguments Ret {A} a.
  Arguments Vis {A X} e k.
  Arguments Iter {A St B} body s k.

  Fixpoint bind {A B : Type} (t : tree A) (f : A -> tree B) : tree B :=
    match t with
    | Ret a => f a
    | Vis e k => Vis e (fun x => bind (k x) f)
    | Iter body s k => Iter body s (fun b => bind (k b) f)
    end.

  Lemma bind_ret {A : Type} (t : tree A) (ext : forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g) :
    bind t (fun a => Ret a) = t.
  Proof.
    induction t; intros; cbn; try reflexivity; f_equal; apply ext; intros; auto.
  Qed.

  Lemma bind_bind {A B C : Type} (t : tree A) (f : A -> tree B) (g : B -> tree C)
      (ext : forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g) :
    bind (bind t f) g = bind t (fun a => bind (f a) g).
  Proof.
    induction t; intros; cbn; try reflexivity; f_equal; apply ext; intros; auto.
  Qed.

  (** ** A program that may throw *)

  Variable exn : Type.

  Definition prog (A : Type) : Type := tree (exn + A).

  Definition ret {A : Type} (a : A) : prog A := Ret (inr a).
  Definition throw {A : Type} (e : exn) : prog A := Ret (inl e).

  (** One effect, done. *)
  Definition perform {X : Type} (e : E X) : prog X := Vis e (fun x => Ret (inr x)).

  (** An effect that itself gives an exception or a value: a call. *)
  Definition attempt {X : Type} (e : E (exn + X)) : prog X := Vis e (fun r => Ret r).

  Definition then_ {A B : Type} (p : prog A) (k : A -> prog B) : prog B :=
    bind p (fun r => match r with inl e => Ret (inl e) | inr a => k a end).

  Definition try_catch {A : Type} (p : prog A) (handler : exn -> prog A) : prog A :=
    bind p (fun r => match r with inl e => handler e | inr a => Ret (inr a) end).

  (** Sequencing that stops at a throw is a monad's: Scala's `flatMap` on what may throw. *)
  Section Laws.

    Hypothesis ext : forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g.

    Lemma ret_then {A B : Type} (a : A) (k : A -> prog B) : then_ (ret a) k = k a.
    Proof. reflexivity. Qed.

    Lemma then_ret {A : Type} (p : prog A) : then_ p (fun a => ret a) = p.
    Proof.
      unfold then_, ret. transitivity (bind p (fun r => Ret r)); [| exact (bind_ret p ext) ].
      f_equal. apply ext. intros [e | a]; reflexivity.
    Qed.

    Lemma then_then {A B C : Type} (p : prog A) (k : A -> prog B) (j : B -> prog C) :
      then_ (then_ p k) j = then_ p (fun a => then_ (k a) j).
    Proof.
      unfold then_. rewrite (bind_bind _ _ _ ext). f_equal. apply ext. intros [e | a]; reflexivity.
    Qed.

  End Laws.

  (** `last` runs however `p` ends; what `p` gave or threw is then given or thrown, unless `last` throws. *)
  Definition try_finally {A : Type} (p : prog A) (last : prog unit) : prog A :=
    bind p (fun r => then_ last (fun _ => Ret r)).

  (** A loop over a state: each turn gives the next state, or what the loop gives; a throw ends it. *)
  Definition loop {St B : Type} (body : St -> prog (St + B)) (s : St) : prog B :=
    Iter (fun s => bind (body s) (fun r => match r with
                                           | inl e => Ret (inr (inl e))
                                           | inr (inl next) => Ret (inl next)
                                           | inr (inr b) => Ret (inr (inr b))
                                           end)) s (fun r => Ret r).

  Definition again {St B : Type} (s : St) : prog (St + B) := ret (inl s).
  Definition leave {St B : Type} (b : B) : prog (St + B) := ret (inr b).

End Tree.

Arguments Ret {E A} a.
Arguments Vis {E A X} e k.
Arguments Iter {E A St B} body s k.
Arguments ret {E exn A} a.
Arguments throw {E exn A} e.
Arguments again {E exn St B} s.
Arguments leave {E exn St B} b.
Arguments bind {E A B} t f.
Arguments perform {E exn X} e.
Arguments attempt {E exn X} e.
Arguments then_ {E exn A B} p k.
Arguments try_catch {E exn A} p handler.
Arguments try_finally {E exn A} p last.
Arguments loop {E exn St B} body s.

Declare Scope effect_scope.
Delimit Scope effect_scope with effect.
Notation "x <- p ;; k" := (then_ p (fun x => k))
  (at level 61, p at next level, right associativity) : effect_scope.
Notation "' pat <- p ;; k" := (then_ p (fun x => match x with pat => k end))
  (at level 61, pat pattern, p at next level, right associativity) : effect_scope.
Notation "p ;;; k" := (then_ p (fun _ => k)) (at level 61, right associativity) : effect_scope.
