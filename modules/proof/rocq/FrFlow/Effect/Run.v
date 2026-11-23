(** A program run, one thread, on a heap: what a tree gives, computed.

    This is the reference a translation is tested against: the tree read from a method, run here, must give what
    the method gives on the JVM. It is no semantics of threads; a run that calls what is outside the code asks
    `outside_run` what that gives.

    An object is its class and what each field holds; a field holds, before it is written, what `initial` says
    (zero, false, no object). Reading or writing a field of no object, or of an object not made, does not run
    (`None`), as does running out of `fuel`. *)

From Stdlib Require Import List.
From FrFlow.Effect Require Import Tree Sig.
Import ListNotations.

Section Run.

  Variables class field method outside : Type.
  Variable field_ty : field -> Type.
  Variables (method_in method_out : method -> Type) (outside_in outside_out : outside -> Type).
  Variable exn : Type.

  Abbreviation eff := (eff class field method outside field_ty method_in method_out outside_in outside_out exn).

  Variable field_eq : forall f g : field, {f = g} + {f <> g}.
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

  Definition read (h : heap) (r : ref) (f : field) : option (field_ty f) :=
    match r with
    | null => None
    | at_ n => option_map (fun o => held o f) (nth_error h n)
    end.

  Definition written (h : heap) (r : ref) (f : field) (v : field_ty f) : option heap :=
    match r with
    | null => None
    | at_ n => option_map (fun o => replaced h n (holding o f v)) (nth_error h n)
    end.

  Variable body : forall m : method, method_in m -> tree eff (exn + method_out m).
  Variable outside_run : forall m : outside, outside_in m -> heap -> option ((exn + outside_out m) * heap).

  Definition done (called : forall m : method, method_in m -> heap -> option ((exn + method_out m) * heap))
      {X : Type} (e : eff X) (h : heap) : option (X * heap) :=
    match e in Sig.eff _ _ _ _ _ _ _ _ _ _ X return option (X * heap) with
    | Get o f => option_map (fun v => (v, h)) (read h o f)
    | Put o f v => option_map (fun h' => (tt, h')) (written h o f v)
    | New c => Some (at_ (length h), h ++ [{| class_of := c; held := initial |}])
    | Call m given => called m given h
    | Ext m given => outside_run m given h
    end.

  Fixpoint run (fuel : nat) {A : Type} (t : tree eff A) (h : heap) {struct fuel} : option (A * heap) :=
    match fuel with
    | O => None
    | S n =>
        match t with
        | Ret a => Some (a, h)
        | Vis e k =>
            match done (fun m given => run n (body m given)) e h with
            | Some (x, h') => run n (k x) h'
            | None => None
            end
        | Iter body_ s k =>
            match run n (body_ s) h with
            | Some (inl next, h') => run n (Iter body_ next k) h'
            | Some (inr b, h') => run n (k b) h'
            | None => None
            end
        end
    end.

  (** What a program gives from a heap with nothing in it. *)
  Definition gives (fuel : nat) {A : Type} (t : tree eff A) : option A := option_map fst (run fuel t []).

End Run.
