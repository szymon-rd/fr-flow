(** A step of the machine, as what it did.

    `Frames.step_thread` computes a step: it names values as it goes and gives an event. Here the same step is
    said by what was done, with the values themselves (`action`): a call responded, a call made, an operation
    on an object. The event is the action written with the references known (`render`), and it stays the same
    however the references grow afterwards (`render_more`). `step_shape` says every step the machine takes is
    one of the three (`shape`), with what the machine checked of it. The laws of an execution are proven from
    that (`Bridge`). *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Scala.Run.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Rules.Walk FrFlow.Code.Witness.
Require Import FrFlow.Bridge.Names FrFlow.Bridge.Checks FrFlow.Bridge.Frames.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** ** What a step did *)

(** By the thread `t`, in its call made at `i`: the call responded with `x`; a call made by the label `m`,
    showing the values `shown`; the operation `o` on an object, which gave `x` and left the state `σ`. *)
Inductive action :=
  | Responds (t : tid) (i : Z) (x : res)
  | Calls (t : tid) (i : Z) (m : string) (shown : list val)
  | Does (t : tid) (i : Z) (X : Type) (o : op X) (x : X) (σ : state).
Arguments Does t i {X} o x σ.

Definition actor (act : action) : tid :=
  match act with Responds t _ _ | Calls t _ _ _ | Does t _ _ _ _ => t end.

Definition within (act : action) : Z :=
  match act with Responds _ i _ | Calls _ i _ _ | Does _ i _ _ _ => i end.

(** The values its event names. *)
Definition mentions (act : action) : list val :=
  match act with
  | Responds t _ x => VTid t :: mentioned x
  | Calls t _ _ shown => VTid t :: shown
  | Does t _ o x σ => VTid t :: op_vals σ o x
  end.

Section Steps.

  Variable T : table.
  Variable known : classes.
  Variable named : string -> list val -> option program.

  (** The event, written with the references `R`. *)
  Definition render (R : list (Z * val)) (act : action) : Event :=
    match act with
    | Responds t i x => Event_Respond (name_of R (VTid t)) i (response R x) []
    | Calls t i m shown => Event_Invoke (name_of R (VTid t)) (Some i) (Invocation_mk m (map (name_of R) shown))
    | Does t i o x σ => op_said T (name_of R (VTid t)) i σ R o x
    end.

  (** ** The event stays as the references grow *)

  Lemma render_more (R more : list (Z * val)) (act : action) :
    (forall v, In v (mentions act) -> has_name R v) -> render (R ++ more) act = render R act.
  Proof.
    intros H. assert (forall v, In v (mentions act) -> name_of (R ++ more) v = name_of R v) as Hn.
    { intros v Hv. apply name_of_more, H, Hv. }
    destruct act as [t i x | t i m shown | t i X o x σ]; cbn [render mentions] in *.
    - rewrite (Hn (VTid t)) by (left; reflexivity). f_equal.
      destruct x as [e | v]; cbn [response mentioned] in *; f_equal; apply Hn; right; left; reflexivity.
    - rewrite (Hn (VTid t)) by (left; reflexivity). do 2 f_equal.
      apply map_ext_in. intros v Hv. apply Hn. right. exact Hv.
    - rewrite (Hn (VTid t)) by (left; reflexivity).
      assert (forall v, In v (op_vals σ o x) -> name_of (R ++ more) v = name_of R v) as Ho.
      { intros v Hv. apply Hn. right. exact Hv. }
      clear Hn H. destruct o; cbn [op_said op_vals] in *; try reflexivity.
      + destruct x as [e | r]; [reflexivity |]. rewrite (Ho (vref cls r)) by (left; reflexivity). f_equal.
        apply map_ext_in. intros fv Hfv. f_equal. apply Ho. right. apply in_map. exact Hfv.
      + destruct x as [e | v]; [reflexivity |].
        rewrite (Ho (vref (class_in σ r) r)) by (left; reflexivity).
        rewrite (Ho v) by (right; left; reflexivity). reflexivity.
      + rewrite (Ho (vref (class_in σ r) r)) by (left; reflexivity). reflexivity.
      + rewrite (Ho (vref (class_in σ r) r)) by (left; reflexivity).
        rewrite (Ho v) by (right; left; reflexivity). reflexivity.
      + rewrite (Ho (vref (class_in σ r) r)) by (left; reflexivity). f_equal.
        destruct x as [e | [v |]]; try reflexivity. f_equal. apply Ho. right. left. reflexivity.
  Qed.

  (** ** The three steps *)

  (** A call made where the program `p` stands: of what is outside the code, by its label, running what the
      library says; of a method; of a function applied. With how the call is kept (`kind`), its label, the
      values it shows, what the laws are asked of it (`act`), the program it runs, and what follows it. *)
  Inductive calls (p : program) : kind -> string -> list val -> option intent -> program -> (res -> program) -> Prop :=
    | calls_outside m args k lp :
        settles T p (Vis (ExtCall 0 m args) k) -> named m args = Some lp ->
        calls p (Outer m) m args None lp k
    | calls_method s on args k :
        settles T p (Call (Method s) (VList (on :: args)) k) ->
        calls p (Meth s) (label_of s) (receiver on ++ args) (Some (method_act known s on args))
          (does T (method_act known s on args)) k
    | calls_function c arg k m :
        settles T p (Call c arg k) -> applied c arg -> called_as c arg m ->
        calls p Func m (VCode c :: arguments arg) (Some (AsFunction c (arguments arg)))
          (does T (AsFunction c (arguments arg))) k.

  (** One step of the thread `t`, in its call `top` with `p` left of it and the calls `under` waiting, at the
      moment `w`: what it did, what the thread becomes, the state, and the threads started. *)
  Inductive shape (w : Z) (nxt : nat) (σ : state) (t : tid) (top : call) (p : program)
      (under : list (call * (res -> program))) : action -> thread -> state -> list thread -> Prop :=
    | shape_respond x :
        settles T p (Ret x) -> answer_ok known top under x = true ->
        shape w nxt σ t top p under (Responds t (made top) x)
          (match under with [] => Done t x | (c, k) :: rest => Active t c (k x) rest end)
          (match under with [] => terminate σ t | _ :: _ => σ end) []
    | shape_call kd m shown act lp k :
        calls p kd m shown act lp k -> agreed T known m shown act = true ->
        shape w nxt σ t top p under (Calls t (made top) m shown)
          (Active t (CallOf w kd) lp ((top, k) :: under)) σ []
    | shape_op X (o : op X) k x σ' :
        settles T p (Vis o k) -> (outside_ top || is_said o) = true ->
        oprun t nxt o σ = Did x σ' -> op_ok T known top σ o x = true ->
        shape w nxt σ t top p under (Does t (made top) o x σ') (Active t top (k x) under) σ' (started σ o).

  Lemma guard_stepped (ok : bool) (why : string) (s : stepped) th σ refs new e :
    guard ok why s = Stepped th σ refs new e -> ok = true /\ s = Stepped th σ refs new e.
  Proof. destruct ok; cbn; [auto | discriminate]. Qed.

  Lemma own_named (refs : list (Z * val)) (t : tid) (vs : list val) :
    name_of (extend (extend refs [VTid t]) vs) (VTid t) = name_of (extend refs [VTid t]) (VTid t).
  Proof.
    destruct (extend_more (extend refs [VTid t]) vs) as [more ->]. apply name_of_more.
    apply extend_names. left. reflexivity.
  Qed.

  (** A thread that ends leaves the objects as they were. *)
  Lemma objects_terminate (σ : state) (t : tid) : s_obj (terminate σ t) = s_obj σ.
  Proof. unfold terminate. destruct (s_th σ t); reflexivity. Qed.

  Lemma placed_terminate (σ : state) (t : tid) (vs : list val) : placed_in (terminate σ t) vs = placed_in σ vs.
  Proof. unfold placed_in. rewrite objects_terminate. reflexivity. Qed.

  (** The references after a step, the objects named, and the event, as `step_thread` builds them. *)
  Ltac built Hp :=
    split; [reflexivity | split; [exact Hp | cbn [render mentions]; rewrite own_named; reflexivity]].

  Lemma push_stepped w σ refs0 t top under kd lp k m shown th' σ' refs' new e :
    push w σ (extend refs0 [VTid t]) t (name_of (extend refs0 [VTid t]) (VTid t)) top under kd lp k m shown
      = Stepped th' σ' refs' new e ->
    th' = Active t (CallOf w kd) lp ((top, k) :: under) /\ σ' = σ /\ new = [] /\
    refs' = extend refs0 (mentions (Calls t (made top) m shown)) /\
    placed_in σ' (mentions (Calls t (made top) m shown)) = true /\
    e = render refs' (Calls t (made top) m shown).
  Proof.
    unfold push. set (refs := extend refs0 [VTid t]). intros H. apply guard_stepped in H as [Hp H].
    injection H as <- <- <- <- <-. subst refs. do 3 (split; [reflexivity |]). built Hp.
  Qed.

  (** Every step the machine takes is one of the three; the references grow by the values its event names,
      each of them an object of the heap of its class; and the event is the action written with them. *)
  Lemma step_shape w nxt σ refs0 t top p under th' σ' refs' new e :
    step_thread T known named w nxt σ refs0 (Active t top p under) = Stepped th' σ' refs' new e ->
    exists act, shape w nxt σ t top p under act th' σ' new /\ refs' = extend refs0 (mentions act) /\
      placed_in σ' (mentions act) = true /\ e = render refs' act.
  Proof.
    cbn [step_thread]. pose proof (settle_settles T 1000 p) as Hs. set (refs := extend refs0 [VTid t]).
    destruct (settle T 1000 p) as [x | X o k | S B body s0 k | c arg k]; intros H.
    - apply guard_stepped in H as [Hans H]. apply guard_stepped in H as [Hp H].
      exists (Responds t (made top) x).
      destruct under as [| [c k] rest]; injection H as <- <- <- <- <-; subst refs;
        [rewrite <- (placed_terminate σ t) in Hp |];
        (split; [exact (shape_respond w nxt σ t top p _ x Hs Hans) | built Hp]).
    - destruct (labelled_call o k) as [[[lbl shown] k1] |] eqn:L.
      + destruct o; try discriminate L. destruct r; [| discriminate L]. cbn in L. injection L as <- <- <-.
        destruct (named method args) as [lp |] eqn:Hn; [| discriminate H].
        apply guard_stepped in H as [Hag H]. subst refs. apply push_stepped in H as (-> & -> & -> & H).
        exists (Calls t (made top) method args).
        split; [exact (shape_call w nxt σ t top p under _ _ _ _ _ _ (calls_outside p _ _ _ _ Hs Hn) Hag) | exact H].
      + destruct (outside_ top || is_said o) eqn:Hsaid; [| discriminate H].
        destruct (oprun t nxt o σ) as [x σ1 | |] eqn:Hop; try discriminate H.
        apply guard_stepped in H as [Hok H]. apply guard_stepped in H as [Hp H]. injection H as <- <- <- <- <-.
        subst refs. exists (Does t (made top) o x σ1).
        split; [exact (shape_op w nxt σ t top p under X o k x σ1 Hs Hsaid Hop Hok) | built Hp].
    - discriminate H.
    - subst refs. destruct c as [d sc group | b sc | s | s on | cls].
      + apply guard_stepped in H as [Hag H]. apply push_stepped in H as (-> & -> & -> & H).
        exists (Calls t (made top) function_apply (VCode (Fn d sc group) :: arguments arg)).
        split; [| exact H]. refine (shape_call w nxt σ t top p under _ _ _ _ _ _ _ Hag).
        refine (calls_function p _ _ _ _ Hs _ _); [exact I | destruct arg; reflexivity].
      + destruct arg as [| | | | | | vs].
        1-6: apply guard_stepped in H as [Hag H]; apply push_stepped in H as (-> & -> & -> & H);
          eexists (Calls t (made top) _ (VCode (Thunk b sc) :: arguments _));
          (split; [| exact H]); refine (shape_call w nxt σ t top p under _ _ _ _ _ _ _ Hag);
          refine (calls_function p _ _ _ _ Hs _ _); [exact I | reflexivity].
        destruct vs as [| v vs]; [discriminate H |].
        apply guard_stepped in H as [Hag H]. apply push_stepped in H as (-> & -> & -> & H).
        eexists (Calls t (made top) _ (VCode (Thunk b sc) :: arguments _)).
        split; [| exact H]. refine (shape_call w nxt σ t top p under _ _ _ _ _ _ _ Hag).
        refine (calls_function p _ _ _ _ Hs _ _); [exact I | reflexivity].
      + destruct arg as [| | | | | | vs]; try discriminate H. destruct vs as [| on args]; [discriminate H |].
        apply guard_stepped in H as [Hag H]. apply push_stepped in H as (-> & -> & -> & H).
        exists (Calls t (made top) (label_of s) (receiver on ++ args)).
        split; [exact (shape_call w nxt σ t top p under _ _ _ _ _ _ (calls_method p s on args k Hs) Hag) | exact H].
      + destruct arg as [| | | | | | vs]; discriminate H.
      + destruct arg as [| | | | | | vs]; discriminate H.
  Qed.

  (** A call the laws are asked of runs what they are asked: not the library's program. *)
  Lemma calls_does (p : program) kd m shown x lp k : calls p kd m shown (Some x) lp k -> lp = does T x.
  Proof. intros H. inversion H; subst; reflexivity. Qed.

  (** Such a call is kept as one of the code: its steps are events. *)
  Lemma calls_inside (p : program) kd m shown x lp k w :
    calls p kd m shown (Some x) lp k -> outside_ (CallOf w kd) = false.
  Proof. intros H. inversion H; subst; reflexivity. Qed.

End Steps.
