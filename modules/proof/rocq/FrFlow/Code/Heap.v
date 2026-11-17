(** What an operation leaves of the objects of the code, and which event says it.

    For the law of what a variable holds (`Conforms.variables_hold`): the heap of the machine changes only where
    an object is made (`Made`), a field is written (`Wrote`), or a mark is put on an object that is no value of
    a field (`Touched`); and an event that says an object is made or written is the event of such an
    operation. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Scala.Run.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Code.Walk FrFlow.Code.Witness.
Require Import FrFlow.Code.Names FrFlow.Code.Checks FrFlow.Code.Frames FrFlow.Code.Steps FrFlow.Code.Kept.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** A variable's field is no mark *)

Lemma append_length (a b : string) : String.length (a ++ b) = (String.length a + String.length b)%nat.
Proof. induction a as [| c a IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma writing_other (name : string) : writing name <> var_field.
Proof. intros E. apply (f_equal String.length) in E. unfold writing in E. rewrite append_length in E. cbn in E. lia. Qed.

Lemma entered_other (name : string) : entered name <> var_field.
Proof. intros E. apply (f_equal String.length) in E. unfold entered in E. rewrite append_length in E. cbn in E. lia. Qed.

Lemma writing_itself (name : string) : writing name <> name.
Proof. intros E. apply (f_equal String.length) in E. unfold writing in E. rewrite append_length in E. cbn in E. lia. Qed.

(** A field written holds what was written. *)
Lemma field_written (fields : list (string * val)) (name : string) (v : val) :
  field (Machine.written fields name v) name = Some v.
Proof.
  unfold Machine.written. rewrite field_without_other by apply writing_itself. apply field_with_same.
Qed.

(** ** What an operation does to the objects *)

Inductive effect :=
  | Nothing
  | Made (cls : string) (fields : list (string * val)) (r : nat)
  | Wrote (r : nat) (f : string) (v : val)
  | Touched (r : nat).

Definition op_effect {X : Type} (o : op X) : X -> effect :=
  match o in Machine.op _ _ X return X -> effect with
  | ObjNew cls fields => fun x => match x with inr r => Made cls fields r | inl _ => Nothing end
  | ObjSet r f v => fun _ => Wrote r f v
  | ObjMark r _ => fun _ => Touched r
  | Enter r _ _ => fun _ => Touched r
  | _ => fun _ => Nothing
  end.

(** The objects are as they were, but for the one at `r`. *)
Definition changed (σ σ' : state) (r : nat) (o : Machine.object code obj) : Prop :=
  forall r', s_obj σ' r' = if Nat.eq_dec r' r then Some o else s_obj σ r'.

Lemma changed_set (σ : state) (r : nat) (o : Machine.object code obj) : changed σ (set_obj σ r o) r o.
Proof. intros r'. reflexivity. Qed.

Lemma changed_same (σ σ' : state) (r : nat) (o : Machine.object code obj) :
  s_obj σ r = Some o -> (forall r', s_obj σ' r' = s_obj σ r') -> changed σ σ' r o.
Proof. intros H Hs r'. rewrite Hs. destruct (Nat.eq_dec r' r) as [-> |]; [exact H | reflexivity]. Qed.

Lemma oprun_effect (t : tid) (nxt : nat) (X : Type) (o : op X) (σ σ' : state) (x : X) :
  oprun t nxt o σ = Did x σ' ->
  match op_effect o x with
  | Nothing => forall r, s_obj σ' r = s_obj σ r
  | Made cls fields r => s_obj σ r = None /\ changed σ σ' r (cls, fields)
  | Wrote r f v => exists cls fs, s_obj σ r = Some (cls, fs) /\ changed σ σ' r (cls, Machine.written fs f v)
  | Touched r => exists cls fs fs',
      s_obj σ r = Some (cls, fs) /\ field fs' var_field = field fs var_field /\ changed σ σ' r (cls, fs')
  end.
Proof.
  intros H. destruct o; cbn [op_effect].
  all: try (cbn in H; unfold waiting, clear_intr in H; crack H; intros r0; reflexivity).
  - cbn in H. destruct (s_obj σ nxt) eqn:E; [discriminate H |]. injection H as <- <-.
    split; [exact E | apply changed_set].
  - cbn in H. destruct (s_obj σ r) as [[cls fields] |] eqn:E; [| discriminate H].
    destruct (writer fields name); [discriminate H |]. injection H as <- <-.
    exists cls, fields, (with_field fields (writing name) (VTid t)).
    split; [reflexivity | split; [apply field_with_other, writing_other | apply changed_set]].
  - cbn in H. destruct (s_obj σ r) as [[cls fields] |] eqn:E; [| discriminate H].
    exists cls, fields. split; [reflexivity |].
    destruct (writer fields name) as [u |]; [destruct (Nat.eqb u t); [| discriminate H] |];
      injection H as <- <-; apply changed_set.
  - cbn in H. destruct (s_obj σ r) as [[cls fields] |] eqn:E; [| discriminate H]. exists cls, fields.
    destruct (field fields name) as [v |].
    { injection H as <- <-. exists fields. split; [reflexivity | split; [reflexivity |]]. apply changed_same; auto. }
    destruct (holder fields name) as [u |].
    2: { injection H as <- <-. exists (with_field fields (entered name) (VTid t)).
         split; [reflexivity | split; [apply field_with_other, entered_other | apply changed_set]]. }
    exists fields. split; [reflexivity | split; [reflexivity |]]. apply changed_same; [exact E |].
    destruct what; unfold waiting, clear_intr in H; crack H; intros r0; reflexivity.
  - discriminate H.
Qed.

Section Heap.

  Variable T : table.
  Variable known : classes.
  Variable R : list (Z * val).

  (** An event that says a field is written is the event of the operation that wrote it. *)
  Lemma write_effect (act : action) b ins yo f y :
    render T R act = Event_Write b ins yo f y ->
    exists t i X (o : op X) x σ r f0 v, act = Does t i o x σ /\ op_effect o x = Wrote r f0 v /\
      yo = name_of R (vref (class_in σ r) r) /\ f = field_label T (class_in σ r) f0 /\ y = name_of R v.
  Proof.
    destruct act as [t j x | t j m shown | t j X o x σ]; cbn; try discriminate.
    destruct o; cbn; try discriminate; try (destruct x; discriminate).
    intros E. injection E as _ _ <- <- <-. exists t, j, _, (ObjSet r name v), x, σ, r, name, v. auto.
  Qed.

  (** An operation that wrote a field has the event that says so. *)
  Lemma wrote_event (a : Value) (i : Z) (σ : state) (X : Type) (o : op X) (x : X) r f v :
    op_effect o x = Wrote r f v ->
    op_said T a i σ R o x = Event_Write a (Some i) (name_of R (vref (class_in σ r) r))
      (field_label T (class_in σ r) f) (name_of R v).
  Proof.
    destruct o; cbn; try discriminate; try (destruct x; discriminate). intros E. injection E as <- <- <-.
    reflexivity.
  Qed.

  (** One that made an object has the event that says so, with what each field holds. *)
  Lemma made_event (a : Value) (i : Z) (σ : state) (X : Type) (o : op X) (x : X) cls fields r :
    op_effect o x = Made cls fields r ->
    op_said T a i σ R o x = Event_Make a (Some i) (name_of R (vref cls r)) cls
      (map (fun fv => Held_mk (field_label T cls (fst fv)) (name_of R (snd fv))) fields) /\
    In (vref cls r) (op_vals σ o x) /\ forall fv, In fv fields -> In (snd fv) (op_vals σ o x).
  Proof.
    destruct o; cbn; try discriminate; destruct x as [e | r0]; try discriminate.
    intros E. injection E as <- <- <-. split; [reflexivity | split; [left; reflexivity |]].
    intros fv Hfv. right. apply in_map. exact Hfv.
  Qed.

  Lemma wrote_named (σ : state) (X : Type) (o : op X) (x : X) r f v :
    op_effect o x = Wrote r f v -> In (vref (class_in σ r) r) (op_vals σ o x) /\ In v (op_vals σ o x).
  Proof.
    destruct o; cbn; try discriminate; try (destruct x; discriminate). intros E. injection E as <- <- <-.
    split; [left; reflexivity | right; left; reflexivity].
  Qed.

  (** What the machine checked of an operation on a variable: it is made with its one field, and written there. *)
  Lemma ok_made (top : call) (σ : state) (X : Type) (o : op X) (x : X) cls fields r :
    op_ok T known top σ o x = true -> op_effect o x = Made cls fields r -> is_var cls = true ->
    exists v, fields = [(var_field, v)].
  Proof.
    destruct o; cbn; try discriminate; destruct x as [e | r0]; try discriminate.
    intros Hok E Hvar. injection E as <- <- <-. rewrite Hvar in Hok. cbn in Hok.
    destruct fields0 as [| [f v] rest]; [discriminate Hok |]. destruct rest; [| discriminate Hok].
    apply String.eqb_eq in Hok. subst f. eauto.
  Qed.

  Lemma ok_wrote (top : call) (σ : state) (X : Type) (o : op X) (x : X) r f v :
    op_ok T known top σ o x = true -> op_effect o x = Wrote r f v -> is_var (class_in σ r) = true ->
    f = var_field.
  Proof.
    destruct o; cbn; try discriminate; try (destruct x; discriminate).
    intros Hok E Hvar. injection E as <- <- <-. rewrite Hvar in Hok. cbn in Hok. apply String.eqb_eq. exact Hok.
  Qed.

  (** An event that says a field is read is the event of the read. *)
  Lemma render_read (act : action) b ins yo f y :
    render T R act = Event_Read b ins yo f y ->
    exists t i r f0 v σ, act = Does t i (ObjGet r f0) (inr v) σ /\
      yo = name_of R (vref (class_in σ r) r) /\ f = field_label T (class_in σ r) f0 /\ y = name_of R v.
  Proof.
    destruct act as [t j x | t j m shown | t j X o x σ]; cbn; try discriminate.
    destruct o; cbn; try discriminate; destruct x as [e | v]; try discriminate.
    intros E. injection E as _ _ <- <- <-. exists t, j, r, name, v, σ. auto.
  Qed.

End Heap.
