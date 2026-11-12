(** Programs over a library's operations: what code that calls a library is read as.

    A program is a tree: it returns, or it calls one operation of the library and goes on with what the
    operation gave, or it loops, or it calls a closure. An operation is one step, taken among the steps of other
    threads. The library's operations (`Op`) and the closures (`code`) are parameters: a program says nothing of
    what they do, only that it calls them.

    Failure is a value: a program that may throw gives an exception or a result (`M` in `Jdk.v`), as FrFlow reads
    a failing call as an `Either`. `try`, `catch` and `finally` are then ordinary functions on programs. *)

Set Implicit Arguments.

Section Prog.

  Variable Op : Type -> Type.     (* the library's operations, each typed by what it gives *)
  Variable code : Type.           (* closures: values that can be called *)
  Variable R : Type.              (* what a call of a closure gives *)

  Inductive prog (A : Type) : Type :=
    | Ret (a : A)
    | Vis (X : Type) (o : Op X) (k : X -> prog A)
    | Iter (S B : Type) (body : S -> prog (S + B)) (s : S) (k : B -> prog A)
    | Call (c : code) (k : R -> prog A).

  Arguments Ret {A} a.
  Arguments Vis {A X} o k.
  Arguments Iter {A S B} body s k.
  Arguments Call {A} c k.

  Fixpoint pbind {A B : Type} (p : prog A) (f : A -> prog B) : prog B :=
    match p with
    | Ret a => f a
    | Vis o k => Vis o (fun x => pbind (k x) f)
    | Iter body s k => Iter body s (fun b => pbind (k b) f)
    | Call c k => Call c (fun r => pbind (k r) f)
    end.

  (** One turn of a loop: its body, then the loop again or what follows it. *)
  Definition unfold_iter {A S B : Type} (body : S -> prog (S + B)) (s : S) (k : B -> prog A) : prog A :=
    pbind (body s) (fun r => match r with inl s' => Iter body s' k | inr b => k b end).

End Prog.

Arguments Ret {Op code R A} a.
Arguments Vis {Op code R A X} o k.
Arguments Iter {Op code R A S B} body s k.
Arguments Call {Op code R A} c k.
