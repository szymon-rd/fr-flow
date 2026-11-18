(** The machine, with its calls kept apart: a run of it is written out as an execution.

    The machine of `FrFlow.Jvm.Machine` runs a call of the code in place: what the method does and what follows
    the call become one program, and where the call began and ended is lost. An execution (`Conforms`) has the
    call as an event, the caller waiting for its response. Here a thread is a stack of calls, each with what is
    left of its program, and every step is one event of an execution:

    - a call of a method or of a function of the code is made: the caller waits, and the call is on top;
    - a call of what is outside the code, named by its label, is made the same way: on top is the program the
      library has for the label (`named`), whose steps are the JDK's own and are no events, but for the objects
      of the code it makes, reads and writes, and for the functions it applies;
    - an operation on an object of the code is its event;
    - a call that ends responds, and its caller goes on.

    What makes no event in an execution makes no step here: a loop's turn, an initialiser run where an object is
    made, an argument a primitive takes by name (`Conforms.settles`).

    A step is taken only where an execution of the code has it (`Checks`): the values are of the types the code
    says, a call runs what the laws of `Conforms` say a call of its label runs, each object named is of its
    class, a variable is read and written as the one field it is. A step that is not so stops the run, saying
    why. `Bridge` proves that the events of a run are an execution of the code.

    `run_frames` runs it, threads in turn, and gives the events with how the run ended. It is the machine the
    meaning of Scala's trees is compared with the JVM on (`OxRunSuite`). *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Scala.Run.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Rules.Walk FrFlow.Code.Witness.
Require Import FrFlow.Bridge.Names FrFlow.Bridge.Checks.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Section Frames.

  Variable T : table.
  Variable known : classes.

  (** What the library runs for a call named by its label. *)
  Variable named : string -> list val -> option Conforms.program.

  Local Abbreviation program := Conforms.program.
  Local Abbreviation res := Conforms.res.
  Local Abbreviation run := (Conforms.run T).

  (** ** Threads *)

  (** How a call was made: by nothing of the execution (a thread's first); by its label, running what the
      library says; as a method, by its definition; as a function applied. *)
  Inductive kind := Root | Outer (label : string) | Meth (s : sym) | Func.

  (** A call: the moment it was made at, and how. A thread's first call is made before any moment. *)
  Record call := CallOf { made : Z; kind_ : kind }.

  (** A call that runs the library's program: its steps are the JDK's own. *)
  Definition outside_ (c : call) : bool :=
    match kind_ c with Root | Outer _ => true | Meth _ | Func => false end.

  (** What the call's result is, by how it was made: of the type its label says. *)
  Definition typed_by (c : call) : res -> Prop :=
    match kind_ c with
    | Outer m => returns known m
    | Meth s => returns known (label_of s)
    | Root | Func => fun _ => True
    end.

  Definition typed_ok (c : call) (x : res) : bool :=
    match kind_ c with
    | Outer m => returns_b known m x
    | Meth s => returns_b known (label_of s) x
    | Root | Func => true
    end.

  (** A thread: the call it is in, what is left of that call's program, and the calls that wait under it, each
      with what it does once answered; or ended, with what it gave. *)
  Inductive thread :=
    | Active (t : tid) (top : call) (left : program) (under : list (call * (res -> program)))
    | Done (t : tid) (gave : res).

  (** What a thread started runs first: the function it was made for, called by nothing of the execution. *)
  Definition root (t : tid) (c : code) : thread :=
    Active t (CallOf (-1) Root)
      (match c with
       | Bound s on => Call (Method s) (VList [on]) (fun r => Ret r)
       | _ => Call c (VList []) (fun r => Ret r)
       end) [].

  (** ** What makes no event *)

  Fixpoint settle (fuel : nat) (p : program) : program :=
    match fuel with
    | O => p
    | S fuel' =>
        match p with
        | Iter body s k => settle fuel' (unfold_iter body s k)
        | Call (Init cls) arg k => settle fuel' (pbind (run (Init cls) arg) k)
        | Call (Thunk b sc) (VList []) k => settle fuel' (pbind (run (Thunk b sc) (VList [])) k)
        | _ => p
        end
    end.

  Lemma settle_settles (fuel : nat) (p : program) : settles T p (settle fuel p).
  Proof.
    revert p. induction fuel as [| fuel IH]; intros p; cbn; [apply settled |].
    destruct p as [x | X o k | S B body s k | c arg k]; try apply settled.
    - apply settles_iter. apply IH.
    - destruct c; try apply settled.
      + destruct arg as [| | | | | | vs]; try apply settled. destruct vs; [| apply settled].
        apply settles_forced. apply IH.
      + apply settles_init. apply IH.
  Qed.

  (** ** Events *)

  Definition class_in (σ : state) (r : nat) : string :=
    match s_obj σ r with Some (cls, _) => cls | None => "" end.

  Definition mentioned (x : res) : list val := match x with inr v => [v] | inl e => [thrown e] end.

  Definition response (refs : list (Z * val)) (x : res) : Response :=
    match x with
    | inr v => Response_Returned (name_of refs v)
    | inl e => Response_Threw (name_of refs (thrown e))
    end.

  (** The operations that are events of an execution: those on the objects of the code. *)
  Definition is_said {X : Type} (o : op X) : bool :=
    match o with
    | ObjNew _ _ | ObjGet _ _ | ObjMark _ _ | ObjSet _ _ _ | Enter _ _ _ => true
    | _ => false
    end.

  (** The values such an operation's event names. *)
  Definition op_vals {X : Type} (σ : state) (o : op X) : X -> list val :=
    match o in Machine.op _ _ X return X -> list val with
    | ObjNew cls fields => fun x => match x with inr r => vref cls r :: map snd fields | inl _ => [] end
    | ObjGet r f => fun x => vref (class_in σ r) r :: match x with inr v => [v] | inl _ => [] end
    | ObjMark r f => fun _ => [vref (class_in σ r) r]
    | ObjSet r f v => fun _ => [vref (class_in σ r) r; v]
    | Enter r f what => fun x => vref (class_in σ r) r :: match x with inr (Some v) => [v] | _ => [] end
    | _ => fun _ => []
    end.

  (** Its event, by the thread `a` in the call made at `i`; nothing happens where the operation is no event. *)
  Definition op_said {X : Type} (a : Value) (i : Z) (σ : state) (refs : list (Z * val)) (o : op X)
      : X -> Event :=
    match o in Machine.op _ _ X return X -> Event with
    | ObjNew cls fields => fun x =>
        match x with
        | inr r => Event_Make a (Some i) (name_of refs (vref cls r)) cls
            (map (fun fv => Held_mk (field_label T cls (fst fv)) (name_of refs (snd fv))) fields)
        | inl _ => Event_Stutter
        end
    | ObjGet r f => fun x =>
        match x with
        | inr v => Event_Read a (Some i) (name_of refs (vref (class_in σ r) r))
            (field_label T (class_in σ r) f) (name_of refs v)
        | inl _ => Event_Stutter
        end
    | ObjMark r f => fun _ =>
        Event_Mark a (Some i) (name_of refs (vref (class_in σ r) r)) (field_label T (class_in σ r) f)
    | ObjSet r f v => fun _ =>
        Event_Write a (Some i) (name_of refs (vref (class_in σ r) r)) (field_label T (class_in σ r) f)
          (name_of refs v)
    | Enter r f what => fun x =>
        Event_Enter a (Some i) (name_of refs (vref (class_in σ r) r)) (field_label T (class_in σ r) f)
          (match x with inr (Some v) => Some (name_of refs v) | _ => None end)
    | _ => fun _ => Event_Stutter
    end.

  (** A call named by its label alone, with what follows it. *)
  Definition labelled_call {X : Type} (o : op X) : (X -> program) -> option (string * list val * (res -> program)) :=
    match o in Machine.op _ _ X return (X -> program) -> option (string * list val * (res -> program)) with
    | ExtCall 0%nat label args => fun k => Some (label, args, k)
    | _ => fun _ => None
    end.

  (** The thread an operation starts. *)
  Definition started {X : Type} (σ : state) (o : op X) : list thread :=
    match o with
    | ThreadStart u =>
        match s_th σ u with
        | Some (Thread c TNew _) => [root u c]
        | _ => []
        end
    | _ => []
    end.

  (** ** What a step is taken on *)

  (** Each object named is one of the heap, of the class it is named with. *)
  Definition placed_in (σ : state) (vs : list val) : bool :=
    forallb (fun v => match v with
      | VObj (Ref c r) => match s_obj σ r with Some (cls, _) => String.eqb cls c | None => false end
      | _ => true
      end) vs.

  (** An operation on an object is one an execution has: a variable is made with its one field, and read and
      written there; what a call of the code reads of a field is of the field's class. *)
  Definition op_ok {X : Type} (top : call) (σ : state) (o : op X) : X -> bool :=
    match o in Machine.op _ _ X return X -> bool with
    | ObjNew cls fields => fun _ =>
        negb (is_var cls) || match fields with [(f, _)] => String.eqb f var_field | _ => false end
    | ObjGet r f => fun x =>
        (negb (is_var (class_in σ r)) || String.eqb f var_field) &&
        (outside_ top || match x with inr v => field_typed_b T known (class_in σ r) f v | inl _ => true end)
    | ObjSet r f _ => fun _ => negb (is_var (class_in σ r)) || String.eqb f var_field
    | _ => fun _ => true
    end.

  (** A call that responds gives what its label says, where a call of the code waits for it. *)
  Definition answer_ok (top : call) (under : list (call * (res -> program))) (x : res) : bool :=
    match under with
    | (c, _) :: _ => outside_ c || typed_ok top x
    | [] => true
    end.

  (** ** One step *)

  Inductive stepped :=
    | Stepped (th : thread) (σ : state) (refs : list (Z * val)) (new : list thread) (e : Event)
    | Idle
    | Stuck (why : string).

  Definition guard (ok : bool) (why : string) (s : stepped) : stepped := if ok then s else Stuck why.

  Definition unplaced : string := "a reference to no object of its class".

  (** A call made at `w` by the thread `t` (named `a`) in the call `top`: it runs `lp`, on top; the event shows
      the values `shown`. *)
  Definition push (w : Z) (σ : state) (refs : list (Z * val)) (t : tid) (a : Value) (top : call)
      (under : list (call * (res -> program))) (c : kind) (lp : program) (k : res -> program) (m : string)
      (shown : list val) : stepped :=
    let refs1 := extend refs shown in
    guard (placed_in σ shown) unplaced
      (Stepped (Active t (CallOf w c) lp ((top, k) :: under)) σ refs1 []
         (Event_Invoke a (Some (made top)) (Invocation_mk m (map (name_of refs1) shown)))).

  (** What a call of a method runs: the method on what it is called on; a function, where it is called on one
      by the method of an interface a function is taken as. *)
  Definition method_act (s : sym) (on : val) (args : list val) : intent :=
    match on with
    | VCode f => if applies known (label_of s) then AsFunction f args else AsMethod s on args
    | _ => AsMethod s on args
    end.

  (** One step of a thread at the moment `w`: the event, and what the thread, the state and the references
      become; or it waits; or why it has no step. `next` is a number no thread and no object has. *)
  Definition step_thread (w : Z) (next : nat) (σ : state) (refs0 : list (Z * val)) (th : thread) : stepped :=
    match th with
    | Done _ _ => Idle
    | Active t top p under =>
        let refs := extend refs0 [VTid t] in
        let a := name_of refs (VTid t) in
        let i := made top in
        match settle 1000 p with
        | Ret x =>
            let refs1 := extend refs (mentioned x) in
            let e := Event_Respond a i (response refs1 x) [] in
            guard (answer_ok top under x) "a result that is not of the type its call gives"
              (guard (placed_in σ (mentioned x)) unplaced
                 (match under with
                  | [] => Stepped (Done t x) (terminate σ t) refs1 [] e
                  | (c, k) :: rest => Stepped (Active t c (k x) rest) σ refs1 [] e
                  end))
        | Vis o k =>
            match labelled_call o k with
            | Some (label, args, k') =>
                match named label args with
                | Some lp =>
                    guard (agreed T known label args None) (disagreement T known label args None)
                      (push w σ refs t a top under (Outer label) lp k' label args)
                | None => Stuck (cat "a call from outside with no meaning in the library: " label)
                end
            | None =>
                if outside_ top || is_said o then
                  match oprun t next o σ with
                  | Did x σ' =>
                      let refs1 := extend refs (op_vals σ' o x) in
                      guard (op_ok top σ o x) "an operation on an object that an execution has not"
                        (guard (placed_in σ' (op_vals σ' o x)) unplaced
                           (Stepped (Active t top (k x) under) σ' refs1 (started σ o)
                              (op_said a i σ' refs1 o x)))
                  | Run.Waits => Idle
                  | Cannot why => Stuck why
                  end
                else Stuck "an operation that is no event, in a call of the code"
            end
        | Call c arg k =>
            match c, arg with
            | Method s, VList (on :: args) =>
                let act := method_act s on args in
                guard (agreed T known (label_of s) (receiver on ++ args) (Some act))
                  (disagreement T known (label_of s) (receiver on ++ args) (Some act))
                  (push w σ refs t a top under (Meth s) (does T act) k (label_of s) (receiver on ++ args))
            | Thunk _ _, VList [] => Stuck "an argument by name that was not evaluated where it stands"
            | Fn _ _ _, _ | Thunk _ _, _ =>
                let m := match c, arg with Thunk _ _, VUnit => by_name_apply | _, _ => function_apply end in
                let act := AsFunction c (arguments arg) in
                guard (agreed T known m (VCode c :: arguments arg) (Some act))
                  (disagreement T known m (VCode c :: arguments arg) (Some act))
                  (push w σ refs t a top under Func (does T act) k m (VCode c :: arguments arg))
            | _, _ => Stuck "a call of what is no method and no function"
            end
        | Iter _ _ _ => Stuck "a loop that makes no event"
        end
    end.

  (** ** Threads in turn *)

  Fixpoint alive_at (ths : list thread) (i : nat) : list (nat * tid) :=
    match ths with
    | [] => []
    | Active t _ _ _ :: rest => (i, t) :: alive_at rest (S i)
    | Done _ _ :: rest => alive_at rest (S i)
    end.

  Fixpoint gave_of (ths : list thread) : list (tid * res) :=
    match ths with
    | [] => []
    | Done t r :: rest => (t, r) :: gave_of rest
    | Active _ _ _ _ :: rest => gave_of rest
    end.

  (** Which thread a turn tries first, as in `Run.run`. *)
  Variable order : nat -> nat.

  (** A step of some thread at each turn. `past` is the events so far, the last first; the moment is how many
      there are. What it gives: how the run ended, the events in order, and the references they name. *)
  Fixpoint run_frames (fuel : nat) (ths : list thread) (σ : state) (refs : list (Z * val))
      (next turn idle : nat) (past : list Event) : verdict * list Event * list (Z * val) :=
    let over (v : verdict) := (v, rev past, refs) in
    match fuel with
    | O => over (Unfinished (gave_of ths))
    | S fuel' =>
        match alive_at ths 0 with
        | [] => over (Finished (gave_of ths) (List.length past))
        | alive =>
            let n := List.length alive in
            if Nat.leb n idle then over (Deadlock (map snd alive) (gave_of ths) (List.length past)) else
            match nth_error alive (Nat.modulo (order turn + idle) n) with
            | Some (i, t) =>
                match nth_error ths i with
                | Some th =>
                    match step_thread (Z.of_nat (List.length past)) next σ refs th with
                    | Stepped th' σ' refs' new e =>
                        run_frames fuel' (firstn i ths ++ th' :: skipn (S i) ths ++ new) σ' refs'
                          (S next) (S turn) 0 (e :: past)
                    | Idle => run_frames fuel' ths σ refs next turn (S idle) past
                    | Stuck why => over (Stopped why t (List.length past))
                    end
                | None => over (Unfinished (gave_of ths))
                end
            | None => over (Unfinished (gave_of ths))
            end
        end
    end.

End Frames.

(** ** A program, started *)

Section Start.

  Variable T : table.
  Variable known : classes.
  Variable named : string -> list val -> option Conforms.program.

  (** The first thread: what `Run.program` does (the object `main` is of, then `main` on it), called by nothing
      of the execution. *)
  Definition first_thread (main : sym) : thread :=
    Active first (CallOf (-1) Root) (Run.program T main) [].

  (** The program run from `main`, for at most `fuel` steps, the threads taking turns as `order` says. *)
  Definition execute_frames (order : nat -> nat) (fuel : nat) (main : sym)
      : verdict * list Event * list (Z * val) :=
    run_frames T known named order fuel [first_thread main] (state0 T (Method main)) []
      (S (List.length (stateful_modules T))) 0 0 [].

End Start.
