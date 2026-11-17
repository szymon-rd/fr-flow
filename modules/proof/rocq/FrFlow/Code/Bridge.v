(** A run of the machine is an execution of the code.

    The machine of `Frames` runs the meaning of the code's trees, one thread's step after another, and writes
    each step as an event. `Conforms` says what it is for the events at each moment to be an execution of the
    code: the laws the model's statements are proven from. Here the two are joined: the events of a run of the
    machine, from any configuration it keeps well (`Kept.inv`), meet the laws that speak of calls, objects made
    and responses (`calls_conform`), under the naming the run's references give.

    The law of what a variable holds (`variables_hold`) is proven of the machine's heap in `Held`.

    What is proven is of the machine. That the machine does what the JVM does is not proven: it is compared with
    the JVM on programs (`OxRunSuite`). *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Scala.Run.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Code.Walk FrFlow.Code.Witness.
Require Import FrFlow.Code.Names FrFlow.Code.Checks FrFlow.Code.Frames FrFlow.Code.Steps FrFlow.Code.Kept.
Require Import FrFlow.Code.Stages FrFlow.Code.Heap.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** ** The threads of a configuration *)

Lemma one_place (c : cfg) (n m : nat) (th th' : thread) :
  NoDup (map tid_of (ths c)) -> nth_error (ths c) n = Some th -> nth_error (ths c) m = Some th' ->
  tid_of th = tid_of th' -> n = m.
Proof.
  intros Hd Hn Hm E. apply (proj1 (NoDup_nth (map tid_of (ths c)) 0%nat) Hd).
  - rewrite length_map. apply nth_error_Some. rewrite Hn. discriminate.
  - rewrite length_map. apply nth_error_Some. rewrite Hm. discriminate.
  - rewrite !(nth_indep _ 0%nat (tid_of th)), !map_nth.
    + rewrite (nth_error_nth _ _ _ Hn), (nth_error_nth _ _ _ Hm). exact E.
    + rewrite length_map. apply nth_error_Some. rewrite Hm. discriminate.
    + rewrite length_map. apply nth_error_Some. rewrite Hn. discriminate.
Qed.

Lemma descending_below (b : Z) (under : list (call * (res -> program))) (c : call) :
  descending b under -> In c (map fst under) -> made c < b.
Proof.
  revert b. induction under as [| [c0 k] rest IH]; intros b H Hin; [destruct Hin |].
  destruct H as [Hc Hrest]. destruct Hin as [<- | Hin]; [exact Hc |]. pose proof (IH _ Hrest Hin). lia.
Qed.

(** Each call a thread is in was made before now. *)
Lemma frames_before (w : Z) (th : thread) (c : call) : stacked w th -> In c (frames th) -> made c < w.
Proof.
  destruct th as [t top p under | t x]; [| intros _ []]. intros [Htop Hdesc] [<- | Hin]; [exact Htop |].
  pose proof (descending_below _ _ _ Hdesc Hin). lia.
Qed.

Section Bridge.

  Variable files : list tree.
  Variable T : table.
  Variable known : classes.
  Variable named : string -> list val -> option program.

  (** ** The events, read back *)

  Section Rendered.

    Variable R : list (Z * val).

    Lemma render_invoke (act : action) a inside m ys :
      render T R act = Event_Invoke a inside (Invocation_mk m ys) ->
      exists t i shown, act = Calls t i m shown /\ a = name_of R (VTid t) /\ ys = map (name_of R) shown.
    Proof.
      destruct act as [t j x | t j m0 shown | t j X o x σ]; cbn.
      - discriminate.
      - intros E. injection E as <- _ <- <-. exists t, j, shown. auto.
      - destruct o; cbn; try discriminate; destruct x; discriminate.
    Qed.

    Lemma render_respond (act : action) a i r sp :
      render T R act = Event_Respond a i r sp ->
      exists t x, act = Responds t i x /\ a = name_of R (VTid t).
    Proof.
      destruct act as [t j x | t j m0 shown | t j X o x σ]; cbn.
      - intros E. injection E as <- <- _ _. exists t, x. auto.
      - discriminate.
      - destruct o; cbn; try discriminate; destruct x; discriminate.
    Qed.

    Lemma render_make (act : action) b inside y cls hs :
      render T R act = Event_Make b inside y cls hs ->
      exists t i fields r σ, act = Does t i (ObjNew cls fields) (inr r) σ /\ y = name_of R (vref cls r).
    Proof.
      destruct act as [t j x | t j m0 shown | t j X o x σ]; cbn; try discriminate.
      destruct o; cbn; try discriminate; destruct x as [e | r0]; try discriminate.
      intros E. injection E as _ _ <- <- _. exists t, j, fields, r0, σ. auto.
    Qed.

    Lemma render_not_atomic (act : action) a inside inv resp sp :
      render T R act <> Event_Atomic a inside inv resp sp.
    Proof.
      destruct act as [t j x | t j m0 shown | t j X o x σ]; cbn; try discriminate.
      destruct o; cbn; try discriminate; destruct x; discriminate.
    Qed.

  End Rendered.

  (** ** A run, place by place *)

  Lemma trace_first w c log cs d : trace T known named w c log cs -> nth 0 cs d = c.
  Proof. destruct 1; reflexivity. Qed.

  Lemma trace_move w c log cs d dl :
    trace T known named w c log cs -> forall j, (j < List.length log)%nat ->
    move T known named (w + Z.of_nat j) (fst (nth j log dl)) (nth j cs d) (snd (nth j log dl)) (nth (S j) cs d).
  Proof.
    induction 1 as [w c | w c n act c1 log cs Hm Htr IH]; intros j Hj; [cbn in Hj; lia |].
    destruct j as [| j].
    - cbn [nth fst snd]. replace (w + Z.of_nat 0) with w by lia. rewrite (trace_first _ _ _ _ d Htr). exact Hm.
    - cbn [nth]. replace (w + Z.of_nat (S j)) with (w + 1 + Z.of_nat j) by lia. apply IH. cbn in Hj. lia.
  Qed.

  (** What a step leaves of the calls of the thread that steps: those it had, or one made now. *)
  Lemma shape_frames w nxt σ t top p under act th' σ' new :
    shape T known named w nxt σ t top p under act th' σ' new ->
    forall c, In c (frames th') -> In c (frames (Active t top p under)) \/ made c = w.
  Proof.
    intros H c Hc. destruct H as [x Hs Hans | kd m shown act' lp k Hcalls Hag | X o k x σ1 Hs Hsaid Hop Hok].
    - destruct under as [| [c0 k0] rest]; [destruct Hc |]. left. right. exact Hc.
    - destruct Hc as [<- | Hc]; [right; reflexivity | left; exact Hc].
    - left. exact Hc.
  Qed.

  (** An operation a step did is one the state allowed, with what it gave. *)
  Definition allowed (nxt : nat) (σ : state) (act : action) : Prop :=
    match act with
    | Does t _ o x σ' => oprun t nxt o σ = Did x σ'
    | _ => True
    end.

  Lemma shape_allowed w nxt σ t top p under act th' σ' new :
    shape T known named w nxt σ t top p under act th' σ' new -> allowed nxt σ act.
  Proof. intros H. destruct H; cbn; auto. Qed.

  (** What the machine checked of an operation a step did. *)
  Definition checked (top : call) (σ : state) (act : action) : Prop :=
    match act with
    | Does _ _ o x _ => op_ok T known top σ o x = true
    | _ => True
    end.

  Lemma shape_checked w nxt σ t top p under act th' σ' new :
    shape T known named w nxt σ t top p under act th' σ' new -> checked top σ act.
  Proof. intros H. destruct H; cbn; auto. Qed.

  (** What a step did to the objects. *)
  Definition act_effect (act : action) : effect :=
    match act with Does _ _ o x _ => op_effect o x | _ => Nothing end.

  (** The state an operation left is the state after the step. *)
  Definition left_by (act : action) (σ' : state) : Prop :=
    match act with Does _ _ _ _ σ1 => σ1 = σ' | _ => True end.

  Lemma shape_effect w nxt σ t top p under act th' σ' new :
    shape T known named w nxt σ t top p under act th' σ' new ->
    left_by act σ' /\
    match act_effect act with
    | Nothing => forall r, s_obj σ' r = s_obj σ r
    | Made cls fields r => s_obj σ r = None /\ changed σ σ' r (cls, fields)
    | Wrote r f v => exists cls fs, s_obj σ r = Some (cls, fs) /\ changed σ σ' r (cls, Machine.written fs f v)
    | Touched r => exists cls fs fs',
        s_obj σ r = Some (cls, fs) /\ field fs' var_field = field fs var_field /\ changed σ σ' r (cls, fs')
    end.
  Proof.
    intros H. destruct H as [x Hs Hans | kd m shown act' lp k Hcalls Hag | X o k x σ1 Hs Hsaid Hop Hok].
    - split; [exact I |]. cbn. intros r. destruct under; [rewrite objects_terminate |]; reflexivity.
    - split; [exact I |]. cbn. reflexivity.
    - split; [reflexivity |]. cbn [act_effect]. exact (oprun_effect _ _ _ _ _ _ _ Hop).
  Qed.

  (** ** One run *)

  Variable c0 : cfg.
  Variable log : list (nat * action).
  Variable cs : list cfg.
  Hypothesis run : trace T known named 0 c0 log cs.
  Hypothesis inv0 : inv 0 c0.

  Local Abbreviation len := (List.length log).

  Definition idle : nat * action := (0%nat, Responds 0%nat 0 (inr VUnit)).

  (** The configuration before the moment `j`, the last one from the end of the run on; which thread stepped
      at `j`, and what it did. *)
  Definition conf (j : nat) : cfg := nth (Nat.min j len) cs c0.
  Definition who (j : nat) : nat := fst (nth j log idle).
  Definition did (j : nat) : action := snd (nth j log idle).

  Lemma conf_move (j : nat) :
    (j < len)%nat -> move T known named (Z.of_nat j) (who j) (conf j) (did j) (conf (S j)).
  Proof.
    intros Hj. unfold conf. rewrite !Nat.min_l by lia. exact (trace_move 0 c0 log cs c0 idle run j Hj).
  Qed.

  Lemma conf_inv (j : nat) : (j <= len)%nat -> inv (Z.of_nat j) (conf j).
  Proof.
    induction j as [| j IH]; intros Hj.
    - unfold conf. cbn [Nat.min]. rewrite (trace_first _ _ _ _ c0 run). exact inv0.
    - replace (Z.of_nat (S j)) with (Z.of_nat j + 1) by lia.
      eapply inv_move; [apply IH; lia | apply conf_move; lia].
  Qed.

  Lemma conf_last (j : nat) : (len <= j)%nat -> conf j = conf len.
  Proof. intros H. unfold conf. rewrite Nat.min_r by lia. rewrite Nat.min_id. reflexivity. Qed.

  (** The references of the whole run. *)
  Definition R : list (Z * val) := refs (conf len).

  Lemma refs_step (j : nat) : (j < len)%nat -> refs (conf (S j)) = extend (refs (conf j)) (mentions (did j)).
  Proof. intros Hj. destruct (conf_move j Hj). assumption. Qed.

  Lemma refs_grow (j : nat) : (j <= len)%nat -> exists more, R = refs (conf j) ++ more.
  Proof.
    intros Hj. remember (len - j)%nat as d eqn:Ed. revert j Hj Ed. induction d as [| d IH]; intros j Hj Ed.
    - assert (j = len) as -> by lia. exists []. rewrite app_nil_r. reflexivity.
    - destruct (IH (S j) ltac:(lia) ltac:(lia)) as [more E]. rewrite (refs_step j ltac:(lia)) in E.
      destruct (extend_more (refs (conf j)) (mentions (did j))) as [more' E']. rewrite E' in E.
      exists (more' ++ more). rewrite app_assoc. exact E.
  Qed.

  (** Each value an event names has its name among them. *)
  Lemma did_named (j : nat) : (j < len)%nat -> forall v, In v (mentions (did j)) -> has_name R v.
  Proof.
    intros Hj v Hv. destruct (refs_grow (S j) ltac:(lia)) as [more ->]. apply has_name_more.
    rewrite (refs_step j Hj). apply extend_names. exact Hv.
  Qed.

  (** The execution: at each moment of the run, what was done then, written with the run's references. *)
  Definition history : Z -> Event := history_of (map (fun na => render T R (snd na)) log).

  Lemma history_at (j : nat) : (j < len)%nat -> history (Z.of_nat j) = render T R (did j).
  Proof.
    intros Hj. unfold history, history_of. destruct (Z.ltb_spec (Z.of_nat j) 0); [lia |]. rewrite Nat2Z.id.
    rewrite (nth_indep _ Event_Stutter (render T R (snd idle))) by (rewrite length_map; exact Hj).
    rewrite (map_nth (fun na => render T R (snd na)) log idle j). reflexivity.
  Qed.

  Lemma history_rest (w : Z) : w < 0 \/ Z.of_nat len <= w -> history w = Event_Stutter.
  Proof.
    intros H. unfold history, history_of. destruct (Z.ltb_spec w 0); [reflexivity |].
    apply nth_overflow. rewrite length_map. lia.
  Qed.

  Lemma happened (w : Z) : history w <> Event_Stutter -> exists j, w = Z.of_nat j /\ (j < len)%nat.
  Proof.
    intros H. destruct (Z_lt_dec w 0); [destruct H; apply history_rest; lia |].
    destruct (Z_lt_dec w (Z.of_nat len)); [| destruct H; apply history_rest; lia]. exists (Z.to_nat w). lia.
  Qed.

  (** ** Who steps *)

  (** The thread that steps at `j`: its top call and what was left of it, what the step did of it, and that
      every other thread is as it was. *)
  Lemma acted (j : nat) :
    (j < len)%nat -> exists top p under th' new,
      nth_error (ths (conf j)) (who j) = Some (Active (actor (did j)) top p under) /\
      within (did j) = made top /\ made top < Z.of_nat j /\ descending (made top) under /\
      shape T known named (Z.of_nat j) (next (conf j)) (heap (conf j)) (actor (did j)) top p under (did j) th'
        (heap (conf (S j))) new /\
      nth_error (ths (conf (S j))) (who j) = Some th' /\ tid_of th' = actor (did j) /\
      (forall m th, m <> who j -> nth_error (ths (conf j)) m = Some th ->
         nth_error (ths (conf (S j))) m = Some th).
  Proof.
    intros Hj. destruct (conf_move j Hj) as [t top p under th' new Hn Hshape Hrefs Hp Hths Hnext].
    pose proof (inv_stacks _ _ (conf_inv j ltac:(lia)) _ (nth_error_In _ _ Hn)) as Hst.
    destruct (shape_thread _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hshape Hst) as (Htid & _ & Hactor & Hwithin).
    destruct Hst as [Htop Hdesc]. rewrite Hactor. exists top, p, under, th', new.
    repeat split; try assumption.
    - rewrite Hths. exact (nth_replaced _ _ _ _ _ Hn).
    - intros m th Hm Hth. rewrite Hths. exact (nth_kept _ _ _ _ _ _ Hm Hth).
  Qed.

  (** A thread keeps its place, and its calls are those it had, or one made at the step. *)
  Lemma place_step (j n : nat) (th : thread) :
    (j < len)%nat -> nth_error (ths (conf j)) n = Some th ->
    exists th', nth_error (ths (conf (S j))) n = Some th' /\ tid_of th' = tid_of th /\
      forall c, In c (frames th') -> In c (frames th) \/ made c = Z.of_nat j.
  Proof.
    intros Hj Hn. destruct (acted j Hj) as (top & p & under & th' & new & Hwho & _ & _ & _ & Hshape & Hafter & Htid & Hrest).
    destruct (Nat.eq_dec n (who j)) as [-> | Hne].
    - rewrite Hwho in Hn. injection Hn as <-. exists th'. split; [exact Hafter | split; [exact Htid |]].
      exact (shape_frames _ _ _ _ _ _ _ _ _ _ _ Hshape).
    - exists th. split; [exact (Hrest _ _ Hne Hn) | split; [reflexivity | auto]].
  Qed.

  (** What holds of a thread's calls at one moment and is kept by a step holds from then on. *)
  Lemma place_later (j0 n : nat) (th0 : thread) (P : thread -> Prop) :
    (j0 <= len)%nat -> nth_error (ths (conf j0)) n = Some th0 -> P th0 ->
    (forall j th th', (j0 <= j < len)%nat -> P th ->
       (forall c, In c (frames th') -> In c (frames th) \/ made c = Z.of_nat j) -> P th') ->
    forall j, (j0 <= j <= len)%nat ->
      exists th, nth_error (ths (conf j)) n = Some th /\ tid_of th = tid_of th0 /\ P th.
  Proof.
    intros Hj0 Hn HP Hkeep j Hj. replace j with (j0 + (j - j0))%nat by lia.
    assert (j0 + (j - j0) <= len)%nat as Hle by lia. revert Hle. generalize (j - j0)%nat as d. clear j Hj.
    induction d as [| d IH]; intros Hle.
    - rewrite Nat.add_0_r. exists th0. auto.
    - destruct (IH ltac:(lia)) as (th & Hth & Htid & Hp).
      destruct (place_step (j0 + d) n th ltac:(lia) Hth) as (th' & Hth' & Htid' & Hframes).
      replace (j0 + S d)%nat with (S (j0 + d)) by lia. exists th'.
      split; [exact Hth' | split; [congruence | exact (Hkeep (j0 + d)%nat th th' ltac:(lia) Hp Hframes)]].
  Qed.

  (** ** The naming *)

  Variable N : naming.
  Hypothesis named_all : forall v, has_name R v -> names N (name_of R v) v.

  Lemma one_thread (t t' : tid) :
    has_name R (VTid t) -> has_name R (VTid t') -> name_of R (VTid t) = name_of R (VTid t') -> t = t'.
  Proof.
    intros H H' E. pose proof (named_all _ H) as A. pose proof (named_all _ H') as B. rewrite E in A.
    pose proof (names_one N _ _ _ A B) as X. injection X as X. exact X.
  Qed.

  Lemma actor_named (j : nat) : (j < len)%nat -> has_name R (VTid (actor (did j))).
  Proof. intros Hj. apply (did_named j Hj). apply actor_mentioned. Qed.

  (** An event a call of the thread `t` makes itself, at a moment of the run: `t` steps then, in that call. *)
  Lemma direct_at (t : tid) (i w : Z) :
    has_name R (VTid t) -> direct (name_of R (VTid t)) i (history w) ->
    exists j, w = Z.of_nat j /\ (j < len)%nat /\ actor (did j) = t /\ within (did j) = i.
  Proof.
    intros Ht Hd. destruct (happened w) as (j & -> & Hj).
    { intros E. rewrite E in Hd. exact Hd. }
    rewrite (history_at j Hj) in Hd. destruct (direct_render T R _ _ _ Hd) as [Ea Ew].
    exists j. repeat split; try assumption. symmetry. exact (one_thread _ _ Ht (actor_named j Hj) Ea).
  Qed.

  (** A call makes no event of its own at or before the moment it is made. *)
  Lemma none_before (t : tid) (i w : Z) :
    has_name R (VTid t) -> w <= i -> ~ direct (name_of R (VTid t)) i (history w).
  Proof.
    intros Ht Hw Hd. destruct (direct_at t i w Ht Hd) as (j & -> & Hj & _ & Hwithin).
    destruct (acted j Hj) as (top & p & under & th' & new & _ & Hmade & Hbefore & _). lia.
  Qed.

  (** Once a call has responded, the thread has it no more, and it makes no event of its own. *)
  Lemma none_after (a : Value) (i k w : Z) r sp :
    history k = Event_Respond a i r sp -> k < w -> ~ direct a i (history w).
  Proof.
    intros Hk Hkw Hd. destruct (happened k) as (jk & -> & Hjk); [rewrite Hk; discriminate |].
    rewrite (history_at jk Hjk) in Hk. destruct (render_respond R _ _ _ _ _ Hk) as (t & x & Edid & ->).
    assert (actor (did jk) = t) as Eactor by (rewrite Edid; reflexivity).
    pose proof (actor_named jk Hjk) as Ht. rewrite Eactor in Ht.
    destruct (direct_at t i w Ht Hd) as (jw & -> & Hjw & Ewactor & Ewithin).
    destruct (acted jk Hjk) as (top & p & under & th' & new & Hwho & Hmade & Hbefore & Hdesc & Hshape & Hafter & Htid & _).
    rewrite Edid in Hshape, Hmade. cbn in Hmade.
    (* after the response the thread has no call made at `i` *)
    assert (forall c, In c (frames th') -> made c <> i) as Hgone.
    { intros c Hc. inversion Hshape as [x0 Hs Hans E1 E2 E3 E4 | |]; subst.
      destruct under as [| [c1 k1] rest]; [destruct Hc |]. destruct Hdesc as [Hc1 Hrest].
      destruct Hc as [<- | Hc]; [lia |]. pose proof (descending_below _ _ _ Hrest Hc). lia. }
    destruct (place_later (S jk) (who jk) th' (fun th => forall c, In c (frames th) -> made c <> i)
      ltac:(lia) Hafter Hgone) with (j := jw) as (th & Hth & Htid' & Hnone).
    { intros j th1 th2 Hj Hp Hframes c Hc. destruct (Hframes c Hc) as [Hin | E]; [exact (Hp c Hin) | lia]. }
    { lia. }
    destruct (acted jw Hjw) as (top2 & p2 & under2 & th2 & new2 & Hwho2 & Hmade2 & _).
    assert (who jw = who jk) as Ew.
    { apply (one_place (conf jw) _ _ _ _ (inv_tids _ _ (conf_inv jw ltac:(lia))) Hwho2 Hth).
      cbn [tid_of]. rewrite Htid', Htid, Eactor. exact Ewactor. }
    rewrite Ew, Hth in Hwho2. injection Hwho2 as ->.
    apply (Hnone top2); [left; reflexivity | congruence].
  Qed.

  (** ** A call the machine made of the code follows its program *)

  (** The thread at the place `n`, the thread `t`, made a call at `j` that the laws are asked of: it runs
      `does T x`, and from then on it is where the machine has it. *)
  Lemma called_follows (j n : nat) (t : tid) (top : call) (lp : program) (k : res -> program)
      (under : list (call * (res -> program))) (kd : kind) :
    (j < len)%nat -> has_name R (VTid t) -> outside_ (CallOf (Z.of_nat j) kd) = false ->
    nth_error (ths (conf (S j))) n = Some (Active t (CallOf (Z.of_nat j) kd) lp ((top, k) :: under)) ->
    follows T known N history (name_of R (VTid t)) (Z.of_nat j) lp.
  Proof.
    intros Hj Ht Hin Hpushed. set (i := Z.of_nat j) in *. set (a := name_of R (VTid t)).
    assert (i = Z.of_nat j) as Ei by reflexivity.
    pose proof (inv_stacks _ _ (conf_inv (S j) ltac:(lia)) _ (nth_error_In _ _ Hpushed)) as [_ Hdesc].
    cbn [made descending] in Hdesc. destruct Hdesc as [Htop Hunder].
    (* from the next moment on, the thread's call made at `i` is this one, a call of the code *)
    assert (forall jw, (S j <= jw <= len)%nat ->
      exists th, nth_error (ths (conf jw)) n = Some th /\ tid_of th = t /\ coded th i) as Hlater.
    { apply (place_later (S j) n _ (fun th => coded th i) ltac:(lia) Hpushed).
      - intros c Hc Ec. cbn [frames map fst] in Hc. destruct Hc as [<- | [<- | Hc]]; [exact Hin | exfalso; lia |].
        pose proof (descending_below _ _ _ Hunder Hc). exfalso. lia.
      - intros jw th1 th2 Hjw Hcoded Hframes c Hc Ec.
        destruct (Hframes c Hc) as [Hold | E]; [exact (Hcoded c Hold Ec) | exfalso; lia]. }
    split; [intros w Hw; exact (none_before t i w Ht Hw) |].
    split; [intros k0 w r sp Hk Hkw; exact (none_after _ _ _ _ _ _ Hk Hkw) |].
    exists (fun w => stage_at known (conf (Z.to_nat w)) n i). split.
    - replace (Z.to_nat (i + 1)) with (S j) by lia. unfold stage_at. rewrite Hpushed. cbn [stage_in made].
      rewrite Z.eqb_refl. reflexivity.
    - intros w Hw. destruct (Nat.lt_ge_cases (Z.to_nat w) len) as [Hlt | Hge].
      + destruct (Hlater (Z.to_nat w) ltac:(lia)) as (th & Hth & Htid & Hcoded).
        replace (Z.to_nat (w + 1)) with (S (Z.to_nat w)) by lia.
        replace (history w) with (render T R (did (Z.to_nat w))).
        2: { rewrite <- (history_at (Z.to_nat w) Hlt). f_equal. lia. }
        subst a. rewrite <- Htid.
        refine (stage_step T known named R N named_all w (who (Z.to_nat w)) n _ _ _ i th _ _ _ Hth _ Hcoded Hw).
        * replace w with (Z.of_nat (Z.to_nat w)) at 1 by lia. apply conf_inv. lia.
        * replace w with (Z.of_nat (Z.to_nat w)) at 1 by lia. apply conf_move. exact Hlt.
        * exact (did_named _ Hlt).
        * rewrite Htid. exact Ht.
      + rewrite (history_rest w) by lia. rewrite (conf_last (Z.to_nat w)), (conf_last (Z.to_nat (w + 1))) by lia.
        assert (forall st, ~ its st a i Event_Stutter) as Hnot.
        { intros st [H | H]; [exact H | destruct st; exact H]. }
        split; [intros H; destruct (Hnot _ H) | reflexivity].
  Qed.

  (** A call made at a moment of the run, read back from its event: who made it, what the machine checked of
      it, and the call on top of that thread at the next moment. *)
  Lemma call_made (w : Z) a inside m ys :
    history w = Event_Invoke a inside (Invocation_mk m ys) ->
    exists j t shown kd act lp k top under p,
      w = Z.of_nat j /\ (j < len)%nat /\ a = name_of R (VTid t) /\ has_name R (VTid t) /\
      Forall2 (names N) ys shown /\ calls T known named p kd m shown act lp k /\
      agreed T known m shown act = true /\
      nth_error (ths (conf (S j))) (who j) = Some (Active t (CallOf (Z.of_nat j) kd) lp ((top, k) :: under)).
  Proof.
    intros He. destruct (happened w) as (j & -> & Hj); [rewrite He; discriminate |].
    rewrite (history_at j Hj) in He. destruct (render_invoke R _ _ _ _ _ He) as (t & i & shown & Edid & -> & ->).
    destruct (acted j Hj) as (top & p & under & th' & new & Hwho & _ & _ & _ & Hshape & Hafter & _).
    pose proof (actor_named j Hj) as Ht. pose proof (did_named j Hj) as Hnames.
    rewrite Edid in Hshape, Ht, Hnames. cbn [actor mentions] in *.
    inversion Hshape as [| kd m0 shown0 act lp k Hcalls Hag E1 E2 E3 E4 |]; subst.
    exists j, t, shown, kd, act, lp, k, top, under, p. repeat split; try assumption.
    apply (names_map R N named_all). intros v Hv. apply Hnames. right. exact Hv.
  Qed.

  (** Each call of a method of the code runs the method. *)
  Lemma run_method_calls : method_calls T known N history.
  Proof.
    intros i a inside s cls r d y ys He Hy Hd.
    destruct (call_made _ _ _ _ _ He) as (j & t & shown & kd & act & lp & k & top & under & p & -> & Hj & -> & Ht &
      Hys & Hcalls & Hag & Hpushed).
    inversion Hys as [| y0 v0 ys0 rest Hy0 Hrest]; subst. pose proof (names_one N _ _ _ Hy0 Hy) as ->.
    destruct (agreed_method T known _ _ _ s cls r d rest Hag eq_refl eq_refl Hd) as [-> Hpassed].
    exists rest. split; [exact Hrest | split; [exact Hpassed |]].
    rewrite (calls_does T known named _ _ _ _ _ _ _ Hcalls) in Hpushed.
    exact (called_follows j _ t top _ k under kd Hj Ht (calls_inside T known named _ _ _ _ _ _ _ _ Hcalls) Hpushed).
  Qed.

  (** Each call of a method of an object alone of its class, with no state, runs the method on the object. *)
  Lemma run_module_calls : module_calls T known N history.
  Proof.
    intros i a inside owner name signature c d ys He Hc Hmod Hat Hd.
    destruct (call_made _ _ _ _ _ He) as (j & t & shown & kd & act & lp & k & top & under & p & -> & Hj & -> & Ht &
      Hys & Hcalls & Hag & Hpushed).
    destruct (agreed_module T known _ _ _ owner name signature c d Hag eq_refl Hc Hmod Hat Hd) as [-> Hpassed].
    exists shown. split; [exact Hys | split; [exact Hpassed |]].
    rewrite (calls_does T known named _ _ _ _ _ _ _ Hcalls) in Hpushed.
    exact (called_follows j _ t top _ k under kd Hj Ht (calls_inside T known named _ _ _ _ _ _ _ _ Hcalls) Hpushed).
  Qed.

  (** Each call that applies a function runs it. *)
  Lemma run_function_calls : function_calls files T known N history.
  Proof.
    intros i a inside m c y ys He Happ Hy _.
    destruct (call_made _ _ _ _ _ He) as (j & t & shown & kd & act & lp & k & top & under & p & -> & Hj & -> & Ht &
      Hys & Hcalls & Hag & Hpushed).
    inversion Hys as [| y0 v0 ys0 rest Hy0 Hrest]; subst. pose proof (names_one N _ _ _ Hy0 Hy) as ->.
    destruct (agreed_function T known _ _ _ c rest Hag Happ eq_refl) as [-> Hgiven].
    exists rest. split; [exact Hrest | split; [exact Hgiven |]].
    rewrite (calls_does T known named _ _ _ _ _ _ _ Hcalls) in Hpushed.
    exact (called_follows j _ t top _ k under kd Hj Ht (calls_inside T known named _ _ _ _ _ _ _ _ Hcalls) Hpushed).
  Qed.

  (** No event of the machine is a call made and responded to at once. *)
  Lemma run_no_atomic (w : Z) a inside inv resp sp : history w <> Event_Atomic a inside inv resp sp.
  Proof.
    intros He. destruct (happened w) as (j & -> & Hj); [rewrite He; discriminate |].
    rewrite (history_at j Hj) in He. exact (render_not_atomic R _ _ _ _ _ _ He).
  Qed.

  Lemma run_never_atomic : never_atomic files T known N history.
  Proof. intros w a inside m ys resp sp He. destruct (run_no_atomic _ _ _ _ _ _ He). Qed.

  (** The machine calls no constructor of a class of the code by its label: it makes the object where it is
      made. *)
  Lemma run_constructor_calls : constructor_calls T known N history.
  Proof.
    split.
    - intros i a inside cls c signature ys He Hc Hmod.
      destruct (call_made _ _ _ _ _ He) as (j & t & shown & kd & act & lp & k & top & under & p & _ & _ & _ & _ &
        _ & _ & Hag & _).
      destruct (agreed_made T known _ _ _ cls signature c Hag eq_refl Hc Hmod).
    - intros w a inside cls c signature ys resp sp He. destruct (run_no_atomic _ _ _ _ _ _ He).
  Qed.

  (** ** Objects made, and responses *)

  Lemma conf_next (j : nat) : (j <= len)%nat -> next (conf j) = (next c0 + j)%nat.
  Proof.
    induction j as [| j IH]; intros Hj.
    - unfold conf. cbn [Nat.min]. rewrite (trace_first _ _ _ _ c0 run). lia.
    - destruct (conf_move j ltac:(lia)) as [? ? ? ? ? ? _ _ _ _ _ Hnext]. rewrite Hnext, IH by lia. lia.
  Qed.

  (** An object made at a moment of the run is at the place that was free then. *)
  Lemma made_at (w : Z) b inside y cls hs :
    history w = Event_Make b inside y cls hs ->
    exists j, w = Z.of_nat j /\ (j < len)%nat /\ names N y (vref cls (next c0 + j)).
  Proof.
    intros He. destruct (happened w) as (j & -> & Hj); [rewrite He; discriminate |].
    rewrite (history_at j Hj) in He.
    destruct (render_make R _ _ _ _ _ _ He) as (t & i & fields & r & σ & Edid & ->).
    exists j. split; [reflexivity | split; [exact Hj |]].
    destruct (acted j Hj) as (top & p & under & th' & new & _ & _ & _ & _ & Hshape & _).
    pose proof (did_named j Hj) as Hnames. rewrite Edid in Hshape, Hnames.
    assert (r = (next c0 + j)%nat) as ->.
    { rewrite <- (conf_next j ltac:(lia)).
      pose proof (shape_allowed _ _ _ _ _ _ _ _ _ _ _ Hshape) as Hop. cbn in Hop.
      destruct (s_obj (heap (conf j)) (next (conf j))); [discriminate Hop |]. injection Hop as <- _. reflexivity. }
    apply named_all, Hnames. right. left. reflexivity.
  Qed.

  Lemma run_made_once : made_once N history.
  Proof.
    split.
    - intros w b inside y cls hs He. destruct (made_at _ _ _ _ _ _ He) as (j & _ & _ & Hy). eauto.
    - intros w w' b inside y cls hs b' inside' cls' hs' He He'.
      destruct (made_at _ _ _ _ _ _ He) as (j & -> & _ & Hy).
      destruct (made_at _ _ _ _ _ _ He') as (j' & -> & _ & Hy').
      pose proof (names_one N _ _ _ Hy Hy') as E. injection E as _ E. lia.
  Qed.

  Lemma run_answered_once : answered_once history.
  Proof.
    split.
    - intros k k' a called r r' sp sp' Hk Hk'.
      destruct (Z.lt_total k k') as [Hlt | [E | Hlt]]; [| exact E |]; exfalso.
      + apply (none_after _ _ _ _ _ _ Hk Hlt). rewrite Hk'. cbn. auto.
      + apply (none_after _ _ _ _ _ _ Hk' Hlt). rewrite Hk. cbn. auto.
    - intros k a called r sp Hk. destruct (happened k) as (j & -> & Hj); [rewrite Hk; discriminate |].
      rewrite (history_at j Hj) in Hk. destruct (render_respond R _ _ _ _ _ Hk) as (t & x & Edid & _).
      destruct (acted j Hj) as (top & p & under & th' & new & _ & Hmade & Hbefore & _).
      rewrite Edid in Hmade. cbn in Hmade. lia.
  Qed.

  (** ** What a variable holds *)

  (** No variable is in the heap the run starts from. *)
  Hypothesis no_variables : forall r cls fs, s_obj (heap c0) r = Some (cls, fs) -> is_var cls = false.

  (** What the field `f` of `yo` holds before the moment `w`, by the events: what was written there last; or,
      nothing having been written there, what the object was made holding. *)
  Definition last_written (w : Z) (yo : Value) (f : string) (y : Value) : Prop :=
    (exists k b ins, k < w /\ history k = Event_Write b ins yo f y /\
       forall k' b' ins' y', k < k' -> k' < w -> history k' <> Event_Write b' ins' yo f y') \/
    ((forall k b ins y', k < w -> history k <> Event_Write b ins yo f y') /\
     exists k b ins cls', history k = Event_Make b ins yo cls' [Held_mk f y]).

  Lemma last_later (w : Z) (yo : Value) (f : string) (y : Value) :
    last_written w yo f y -> (forall b ins y', history w <> Event_Write b ins yo f y') ->
    last_written (w + 1) yo f y.
  Proof.
    intros [(k & b & ins & Hk & He & Hno) | [Hno Hmade]] Hnot.
    - left. exists k, b, ins. split; [lia | split; [exact He |]]. intros k' b' ins' y' H1 H2.
      destruct (Z.eq_dec k' w) as [-> |]; [apply Hnot | apply Hno; lia].
    - right. split; [| exact Hmade]. intros k b ins y' Hk.
      destruct (Z.eq_dec k w) as [-> |]; [apply Hnot | apply Hno; lia].
  Qed.

  Definition var_label (cls : string) : string := field_label T cls var_field.

  (** Each variable of the heap holds what was last written to it. *)
  Definition variables_at (j : nat) : Prop :=
    forall r cls fs, s_obj (heap (conf j)) r = Some (cls, fs) -> is_var cls = true ->
      has_name R (vref cls r) /\
      exists v, field fs var_field = Some v /\ has_name R v /\
        last_written (Z.of_nat j) (name_of R (vref cls r)) (var_label cls) (name_of R v).

  (** Each field written so far is a field of an object of the heap. *)
  Definition writes_at (j : nat) : Prop :=
    forall k b ins yo f y, k < Z.of_nat j -> history k = Event_Write b ins yo f y ->
      exists cls r fs, names N yo (vref cls r) /\ s_obj (heap (conf j)) r = Some (cls, fs).

  Lemma one_object (cls cls' : string) (r r' : nat) :
    has_name R (vref cls r) -> has_name R (vref cls' r') ->
    name_of R (vref cls r) = name_of R (vref cls' r') -> cls = cls' /\ r = r'.
  Proof.
    intros H H' E. pose proof (named_all _ H) as A. pose proof (named_all _ H') as B. rewrite E in A.
    pose proof (names_one N _ _ _ A B) as X. injection X as -> ->. auto.
  Qed.

  Lemma changed_at (σ σ' : state) (r : nat) (o : Machine.object code obj) : changed σ σ' r o -> s_obj σ' r = Some o.
  Proof. intros H. rewrite (H r). destruct (Nat.eq_dec r r); [reflexivity | congruence]. Qed.

  Lemma changed_other (σ σ' : state) (r r' : nat) (o : Machine.object code obj) :
    changed σ σ' r o -> r' <> r -> s_obj σ' r' = s_obj σ r'.
  Proof. intros H Hne. rewrite (H r'). destruct (Nat.eq_dec r' r); [contradiction | reflexivity]. Qed.

  Lemma heap_step (j : nat) :
    (j < len)%nat -> variables_at j /\ writes_at j -> variables_at (S j) /\ writes_at (S j).
  Proof.
    intros Hj [HV HW].
    destruct (acted j Hj) as (top & p & under & th' & new & _ & _ & _ & _ & Hshape & _).
    destruct (shape_effect _ _ _ _ _ _ _ _ _ _ _ Hshape) as [Hleft Heff].
    pose proof (shape_checked _ _ _ _ _ _ _ _ _ _ _ Hshape) as Hok.
    destruct (shape_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hshape) as (_ & Hkept & _).
    pose proof (history_at j Hj) as He. pose proof (did_named j Hj) as Hnames.
    set (σ := heap (conf j)) in *. set (σ' := heap (conf (S j))) in *.
    (* a write at this moment is the write the step did *)
    assert (forall b ins yo f y, history (Z.of_nat j) = Event_Write b ins yo f y ->
      exists r f0 v, act_effect (did j) = Wrote r f0 v /\ yo = name_of R (vref (class_in σ' r) r) /\
        f = field_label T (class_in σ' r) f0 /\ y = name_of R v /\
        has_name R (vref (class_in σ' r) r) /\ has_name R v) as Hwrite.
    { intros b ins yo f y Hev. rewrite He in Hev.
      destruct (write_effect T R _ _ _ _ _ _ Hev) as (t & i & X & o & x & σ1 & r & f0 & v & Edid & Eeff & -> & -> & ->).
      rewrite Edid in Hleft, Hnames |- *. cbn in Hleft. subst σ1. cbn [act_effect].
      destruct (wrote_named σ' X o x r f0 v Eeff) as [H1 H2].
      exists r, f0, v. repeat split; try assumption; apply Hnames; right; assumption. }
    split.
    2: { intros k b ins yo f y Hk Hev. destruct (Z.eq_dec k (Z.of_nat j)) as [-> | Hne].
         - destruct (Hwrite _ _ _ _ _ Hev) as (r & f0 & v & Eeff & -> & _ & _ & Hr & _). rewrite Eeff in Heff.
           destruct Heff as (cls & fs & Hobj & Hch). pose proof (changed_at _ _ _ _ Hch) as Hafter.
           exists cls, r, (Machine.written fs f0 v). split; [| exact Hafter].
           assert (class_in σ' r = cls) as Ec by (unfold class_in; rewrite Hafter; reflexivity).
           rewrite Ec in Hr |- *. exact (named_all _ Hr).
         - destruct (HW k b ins yo f y ltac:(lia) Hev) as (cls & r & fs & Hyo & Hobj).
           destruct (Hkept _ _ _ Hobj) as [fs' Hobj']. exists cls, r, fs'. auto. }
    intros r cls fs' Hr Hvar. change (s_obj σ' r = Some (cls, fs')) in Hr.
    replace (Z.of_nat (S j)) with (Z.of_nat j + 1) by lia.
    (* an object the step left as it was holds what it held *)
    assert (forall fs, s_obj σ r = Some (cls, fs) -> field fs' var_field = field fs var_field ->
      (forall b ins y', history (Z.of_nat j) <> Event_Write b ins (name_of R (vref cls r)) (var_label cls) y') ->
      has_name R (vref cls r) /\ exists v, field fs' var_field = Some v /\ has_name R v /\
        last_written (Z.of_nat j + 1) (name_of R (vref cls r)) (var_label cls) (name_of R v)) as Hsame.
    { intros fs Hbefore Hfield Hnot. destruct (HV r cls fs Hbefore Hvar) as (Hnamed & v & Hv & Hvn & Hlast).
      split; [exact Hnamed |]. exists v. rewrite Hfield.
      split; [exact Hv | split; [exact Hvn | exact (last_later _ _ _ _ Hlast Hnot)]]. }
    destruct (act_effect (did j)) as [| c fields r0 | r0 f0 v0 | r0] eqn:Eeff.
    - apply (Hsame fs'); [rewrite <- (Heff r); exact Hr | reflexivity |].
      intros b ins y' Hev. destruct (Hwrite _ _ _ _ _ Hev) as (? & ? & ? & E & _). discriminate E.
    - destruct Heff as [Hfree Hch]. destruct (Nat.eq_dec r r0) as [-> | Hne].
      + rewrite (changed_at _ _ _ _ Hch) in Hr. injection Hr as <- <-.
        destruct (did j) as [t i x | t i m shown | t i X o x σ1] eqn:Edid; try discriminate Eeff.
        cbn in Hleft, Hok, Eeff. subst σ1.
        destruct (ok_made T known top σ X o x c fields r0 Hok Eeff Hvar) as [v ->].
        destruct (made_event T R (name_of R (VTid t)) i σ' X o x c _ r0 Eeff) as (Hev & Hobj & Hfields).
        cbn [render] in He. rewrite Hev in He. cbn [map fst snd] in He.
        assert (has_name R (vref c r0)) as Hnamed by (apply Hnames; right; exact Hobj).
        assert (has_name R v) as Hvn by (apply Hnames; right; exact (Hfields (var_field, v) (or_introl eq_refl))).
        split; [exact Hnamed |]. exists v. split; [reflexivity | split; [exact Hvn |]].
        right. split.
        * intros k b ins y' Hk Hw. destruct (Z.eq_dec k (Z.of_nat j)) as [-> | Hnk]; [rewrite He in Hw; discriminate Hw |].
          destruct (HW k b ins _ _ _ ltac:(lia) Hw) as (cls1 & r1 & fs1 & Hyo & Hobj1).
          pose proof (names_one N _ _ _ (named_all _ Hnamed) Hyo) as E. injection E as _ <-.
          pose proof (eq_trans (eq_sym Hobj1) Hfree) as Hboth. discriminate Hboth.
        * exists (Z.of_nat j), (name_of R (VTid t)), (Some i), c. exact He.
      + apply (Hsame fs'); [rewrite <- (changed_other _ _ _ _ _ Hch Hne); exact Hr | reflexivity |].
        intros b ins y' Hev. destruct (Hwrite _ _ _ _ _ Hev) as (? & ? & ? & E & _). discriminate E.
    - destruct Heff as (cls0 & fs0 & Hobj0 & Hch). destruct (Nat.eq_dec r r0) as [-> | Hne].
      + rewrite (changed_at _ _ _ _ Hch) in Hr. injection Hr as <- <-.
        destruct (HV r0 cls0 fs0 Hobj0 Hvar) as (Hnamed & _).
        destruct (did j) as [t i x | t i m shown | t i X o x σ1] eqn:Edid; try discriminate Eeff.
        cbn in Hleft, Hok, Eeff. subst σ1.
        assert (class_in σ r0 = cls0) as Ec by (unfold class_in; rewrite Hobj0; reflexivity).
        assert (class_in σ' r0 = cls0) as Ec'.
        { unfold class_in. rewrite (changed_at _ _ _ _ Hch). reflexivity. }
        assert (f0 = var_field) as -> by (apply (ok_wrote T known top σ X o x r0 f0 v0 Hok Eeff); rewrite Ec; exact Hvar).
        pose proof (wrote_event T R (name_of R (VTid t)) i σ' X o x r0 var_field v0 Eeff) as Hev.
        destruct (wrote_named σ' X o x r0 var_field v0 Eeff) as [_ Hv0].
        cbn [render] in He. rewrite Hev, Ec' in He.
        split; [exact Hnamed |]. exists v0.
        split; [apply field_written | split; [apply Hnames; right; exact Hv0 |]].
        left. exists (Z.of_nat j), (name_of R (VTid t)), (Some i).
        split; [lia | split; [exact He |]]. intros k' b' ins' y' H1 H2. lia.
      + apply (Hsame fs'); [rewrite <- (changed_other _ _ _ _ _ Hch Hne); exact Hr | reflexivity |].
        intros b ins y' Hev. destruct (Hwrite _ _ _ _ _ Hev) as (r1 & f1 & v1 & E & Eyo & _ & _ & Hr1 & _).
        injection E as <- _ _. destruct (HV r cls fs' (eq_trans (eq_sym (changed_other _ _ _ _ _ Hch Hne)) Hr) Hvar) as (Hnamed & _).
        destruct (one_object _ _ _ _ Hnamed Hr1 Eyo) as [_ E]. exact (Hne E).
    - destruct Heff as (cls0 & fs0 & fs1 & Hobj0 & Hfield & Hch). destruct (Nat.eq_dec r r0) as [-> | Hne].
      + rewrite (changed_at _ _ _ _ Hch) in Hr. injection Hr as <- <-.
        apply (Hsame fs0); [exact Hobj0 | exact Hfield |].
        intros b ins y' Hev. destruct (Hwrite _ _ _ _ _ Hev) as (? & ? & ? & E & _). discriminate E.
      + apply (Hsame fs'); [rewrite <- (changed_other _ _ _ _ _ Hch Hne); exact Hr | reflexivity |].
        intros b ins y' Hev. destruct (Hwrite _ _ _ _ _ Hev) as (? & ? & ? & E & _). discriminate E.
  Qed.

  Lemma heap_kept (j : nat) : (j <= len)%nat -> variables_at j /\ writes_at j.
  Proof.
    induction j as [| j IH]; intros Hj.
    - split.
      + intros r cls fs Hr Hvar. unfold conf in Hr. cbn [Nat.min] in Hr. rewrite (trace_first _ _ _ _ c0 run) in Hr.
        rewrite (no_variables _ _ _ Hr) in Hvar. discriminate Hvar.
      + intros k b ins yo f y Hk Hev. rewrite (history_rest k) in Hev by lia. discriminate Hev.
    - apply heap_step; [lia | apply IH; lia].
  Qed.

  (** What is read of a variable is what was last written to it, or what it was made holding. *)
  Lemma run_variables_hold : variables_hold N history.
  Proof.
    intros w a inside yo f y cls r He Hyo Hvar _ Hwrites.
    destruct (happened w) as (j & -> & Hj); [rewrite He; discriminate |].
    rewrite (history_at j Hj) in He.
    destruct (render_read T R _ _ _ _ _ _ He) as (t & i & r0 & f0 & v & σ1 & Edid & -> & -> & ->).
    destruct (acted j Hj) as (top & p & under & th' & new & _ & _ & _ & _ & Hshape & _).
    pose proof (shape_allowed _ _ _ _ _ _ _ _ _ _ _ Hshape) as Hop.
    pose proof (shape_checked _ _ _ _ _ _ _ _ _ _ _ Hshape) as Hok.
    pose proof (did_named j Hj) as Hnames. rewrite Edid in Hop, Hok, Hnames. cbn in Hop, Hok, Hnames.
    destruct (s_obj (heap (conf j)) r0) as [[cls0 fields] |] eqn:Hobj; [| discriminate Hop].
    destruct (writer fields f0); [discriminate Hop |].
    destruct (field fields f0) as [v' |] eqn:Hfield; [| discriminate Hop]. injection Hop as -> <-.
    assert (class_in (heap (conf j)) r0 = cls0) as Ec by (unfold class_in; rewrite Hobj; reflexivity).
    rewrite Ec in *.
    pose proof (names_one N _ _ _ (named_all _ (Hnames _ (or_intror (or_introl eq_refl)))) Hyo) as E.
    injection E as -> ->.
    rewrite Hvar in Hok. cbn in Hok. apply andb_true_iff in Hok as [Hf _]. apply String.eqb_eq in Hf. subst f0.
    destruct (proj1 (heap_kept j ltac:(lia)) r cls fields Hobj Hvar) as (_ & v0 & Hv0 & _ & Hlast).
    rewrite Hfield in Hv0. injection Hv0 as <-.
    destruct Hlast as [(k & b & ins & Hk & Hev & Hno) | [Hno Hmade]].
    - left. exists k, ins. rewrite <- (Hwrites k b ins _ _ Hev). auto.
    - right. auto.
  Qed.

End Bridge.
