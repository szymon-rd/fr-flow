(** A program run, one thread, on a heap: what a tree gives, computed.

    This is the reference a translation is tested against: the tree read from a method, run here, must give what
    the method gives on the JVM. It is no semantics of threads; a run that calls what is outside the code asks
    `outside_run` what that gives.

    An object is its class and what each field holds; a field holds, before it is written, what `initial` says
    (zero, false, no object). A run ends one of three ways (`ran`):

    - `Gave`: it gave a value, or threw what the tree throws, and left a heap.
    - `Stuck`: it came to what a tree has no node for. A field read or written, or a method called, on no
      object: there the JVM throws `NullPointerException`, which the trees do not have yet. Or on an object
      that was not made, or one of another class than the field's or the method's: code that Scala typed does
      neither. Or `outside_run` gave nothing.
    - `Spent`: the fuel ran out. More fuel may give more: a run that gave something gives it with any more
      fuel (`run_more`). *)

From Stdlib Require Import List.
From FrFlow.Effect Require Import Tree Sig.
Import ListNotations.

Inductive ran (R : Type) : Type :=
  | Gave (r : R)
  | Stuck
  | Spent.

Arguments Gave {R} r.
Arguments Stuck {R}.
Arguments Spent {R}.

Section Run.

  Variables class field method outside : Type.
  Variable field_ty : field -> Type.
  Variables (method_in method_out : method -> Type) (outside_in outside_out : outside -> Type).
  Variable exn : Type.

  Abbreviation eff := (eff class field method outside field_ty method_in method_out outside_in outside_out exn).

  Variable class_eq : forall c d : class, {c = d} + {c <> d}.
  Variable field_eq : forall f g : field, {f = g} + {f <> g}.
  (** The class a field is of, and a method. *)
  Variable field_of : field -> class.
  Variable method_of : method -> class.
  Variable initial : forall f : field, field_ty f.

  Record object : Type := { class_of : class; held : forall f : field, field_ty f }.

  Definition heap : Type := list object.

  Definition holding (o : object) (f : field) (v : field_ty f) : object :=
    {| class_of := class_of o;
       held := fun g => match field_eq f g with
                        | left same => eq_rect f field_ty v g same
                        | right _ => held o g
                        end |}.

  Fixpoint replaced (h : heap) (n : nat) (o : object) : heap :=
    match h, n with
    | [], _ => []
    | _ :: rest, O => o :: rest
    | first :: rest, S m => first :: replaced rest m o
    end.

  (** The object a reference is to, if it is one of class `c`. *)
  Definition found (h : heap) (r : ref) (c : class) : option object :=
    match r with
    | null => None
    | at_ n => match nth_error h n with
               | Some o => if class_eq (class_of o) c then Some o else None
               | None => None
               end
    end.

  Definition read (h : heap) (r : ref) (f : field) : option (field_ty f) :=
    option_map (fun o => held o f) (found h r (field_of f)).

  Definition written (h : heap) (r : ref) (f : field) (v : field_ty f) : option heap :=
    match r with
    | null => None
    | at_ n => option_map (fun o => replaced h n (holding o f v)) (found h r (field_of f))
    end.

  Variable body : forall m : method, ref -> method_in m -> tree eff (exn + method_out m).
  Variable outside_run : forall m : outside, outside_in m -> heap -> option ((exn + outside_out m) * heap).

  Definition or_stuck {R : Type} (r : option R) : ran R :=
    match r with
    | Some x => Gave x
    | None => Stuck
    end.

  Definition done (called : forall m : method, ref -> method_in m -> heap -> ran ((exn + method_out m) * heap))
      {X : Type} (e : eff X) (h : heap) : ran (X * heap) :=
    match e in Sig.eff _ _ _ _ _ _ _ _ _ _ X return ran (X * heap) with
    | Get o f => or_stuck (option_map (fun v => (v, h)) (read h o f))
    | Put o f v => or_stuck (option_map (fun h' => (tt, h')) (written h o f v))
    | New c => Gave (at_ (length h), h ++ [{| class_of := c; held := initial |}])
    | Call o m given => match found h o (method_of m) with
                        | Some _ => called m o given h
                        | None => Stuck
                        end
    | Ext m given => or_stuck (outside_run m given h)
    end.

  Fixpoint run (fuel : nat) {A : Type} (t : tree eff A) (h : heap) {struct fuel} : ran (A * heap) :=
    match fuel with
    | O => Spent
    | S n =>
        match t with
        | Ret a => Gave (a, h)
        | Vis e k =>
            match done (fun m o given => run n (body m o given)) e h with
            | Gave (x, h') => run n (k x) h'
            | Stuck => Stuck
            | Spent => Spent
            end
        | Iter body_ s k =>
            match run n (body_ s) h with
            | Gave (inl next, h') => run n (Iter body_ next k) h'
            | Gave (inr b, h') => run n (k b) h'
            | Stuck => Stuck
            | Spent => Spent
            end
        end
    end.

  Lemma run_step (n : nat) (A : Type) (t : tree eff A) (h : heap) :
    run (S n) t h = match t with
                    | Ret a => Gave (a, h)
                    | Vis e k =>
                        match done (fun m o given => run n (body m o given)) e h with
                        | Gave (x, h') => run n (k x) h'
                        | Stuck => Stuck
                        | Spent => Spent
                        end
                    | Iter body_ s k =>
                        match run n (body_ s) h with
                        | Gave (inl next, h') => run n (Iter body_ next k) h'
                        | Gave (inr b, h') => run n (k b) h'
                        | Stuck => Stuck
                        | Spent => Spent
                        end
                    end.
  Proof. reflexivity. Qed.

  (** A run that did not run out of fuel ends the same way with one more unit of it. *)
  Lemma run_next (fuel : nat) :
    forall (A : Type) (t : tree eff A) (h : heap), run fuel t h <> Spent -> run (S fuel) t h = run fuel t h.
  Proof.
    induction fuel as [| n IH]; intros A t h Hran; [ now contradiction Hran |].
    rewrite (run_step (S n)). rewrite (run_step n) in *.
    destruct t as [a | X e k | St B body_ s k]; [ reflexivity | |].
    - assert (Hdone : done (fun m o given => run n (body m o given)) e h <> Spent ->
          done (fun m o given => run (S n) (body m o given)) e h
            = done (fun m o given => run n (body m o given)) e h).
      { destruct e; cbn [done]; try reflexivity. destruct (found h o (method_of m)); [| reflexivity ].
        intros Hcall. now apply IH. }
      destruct (done (fun m o given => run n (body m o given)) e h) as [[x h'] | |] eqn:Hd.
      + rewrite Hdone by discriminate. now apply IH.
      + now rewrite Hdone by discriminate.
      + now contradiction Hran.
    - destruct (run n (body_ s) h) as [[[next | b] h'] | |] eqn:Hturn.
      + rewrite IH by (rewrite Hturn; discriminate). rewrite Hturn. now apply IH.
      + rewrite IH by (rewrite Hturn; discriminate). rewrite Hturn. now apply IH.
      + rewrite IH by (rewrite Hturn; discriminate). now rewrite Hturn.
      + now contradiction Hran.
  Qed.

  (** With more fuel a run that did not run out ends as it did: what a run gave does not depend on the fuel. *)
  Lemma run_more (fuel more : nat) (A : Type) (t : tree eff A) (h : heap) :
    run fuel t h <> Spent -> run (more + fuel) t h = run fuel t h.
  Proof.
    intros Hran. induction more as [| m IH]; [ reflexivity |].
    cbn [Nat.add]. rewrite run_next; [ exact IH | now rewrite IH ].
  Qed.

  (** What a program gives from a heap with nothing in it. *)
  Definition gives (fuel : nat) {A : Type} (t : tree eff A) : ran A :=
    match run fuel t [] with
    | Gave (a, _) => Gave a
    | Stuck => Stuck
    | Spent => Spent
    end.

End Run.
