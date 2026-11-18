(** Where a call is, in a configuration of the machine; and that each step takes it there as an execution says.

    `Conforms.follows` asks, of a call of the code, a stage before each moment: running what is left of its
    program, waiting for a call it made, or ended. The machine has it: the call is a thread's top call with its
    program, or waits under another, or is gone (`stage_at`). `stage_step` is the heart of the bridge: a step of
    the machine takes each call of the code from its stage to its next by the very rule `Conforms.takes` has for
    the step's event, and leaves every other call where it is. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Scala.Run.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Rules.Walk FrFlow.Code.Witness.
Require Import FrFlow.Bridge.Names FrFlow.Bridge.Checks FrFlow.Bridge.Frames FrFlow.Bridge.Steps FrFlow.Bridge.Kept.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Lemma actor_mentioned (act : action) : In (VTid (actor act)) (mentions act).
Proof. destruct act; left; reflexivity. Qed.

Section Stages.

  Variable T : table.
  Variable known : classes.
  Variable named : string -> list val -> option program.

  (** The references of the whole run, and the naming they give. *)
  Variable R : list (Z * val).
  Variable N : naming.
  Hypothesis named_all : forall v, has_name R v -> names N (name_of R v) v.

  (** ** Events and names *)

  Lemma names_map (vs : list val) :
    (forall v, In v vs -> has_name R v) -> Forall2 (names N) (map (name_of R) vs) vs.
  Proof.
    induction vs as [| v rest IH]; intros H; cbn; constructor.
    - apply named_all, H. left. reflexivity.
    - apply IH. intros u Hu. apply H. right. exact Hu.
  Qed.

  Lemma gives_response (x : res) : (forall v, In v (mentioned x) -> has_name R v) -> gives N (response R x) x.
  Proof. intros H. destruct x as [e | v]; cbn; apply named_all, H; left; reflexivity. Qed.

  Lemma typed_ok_sound (c : call) (x : res) : typed_ok known c x = true -> typed_by known c x.
  Proof.
    unfold typed_ok, typed_by. destruct (kind_ c); try (intros _; exact I); apply returns_b_sound.
  Qed.

  (** An event a call makes itself is of the thread that acts, in the call it is in. *)
  Lemma direct_render (a : Value) (i : Z) (act : action) :
    direct a i (render T R act) -> a = name_of R (VTid (actor act)) /\ within act = i.
  Proof.
    destruct act as [t j x | t j m shown | t j X o x σ]; cbn.
    - intros [-> ->]. auto.
    - intros [-> E]. injection E as ->. auto.
    - destruct o; cbn; try contradiction.
      + destruct x; cbn; [contradiction |]. intros [-> E]. injection E as ->. auto.
      + destruct x; cbn; [contradiction |]. intros [-> E]. injection E as ->. auto.
      + intros [-> E]. injection E as ->. auto.
      + intros [-> E]. injection E as ->. auto.
      + intros [-> E]. injection E as ->. auto.
  Qed.

  (** The response a call waits for is the response of the thread that acts, of the call it is in. *)
  Lemma answers_render (st : stage) (a : Value) (act : action) :
    answers st a (render T R act) ->
    exists called typed k x, st = Waiting called typed k /\ act = Responds (actor act) called x /\
      a = name_of R (VTid (actor act)).
  Proof.
    destruct st as [p | called typed k | |]; try contradiction.
    destruct act as [t j x | t j m shown | t j X o x σ]; cbn.
    - intros [-> ->]. exists called, typed, k, x. auto.
    - contradiction.
    - destruct o; cbn; try contradiction; destruct x; cbn; contradiction.
  Qed.

  Lemma held_all (cls : string) (fields : list (string * val)) :
    (forall fv, In fv fields -> has_name R (snd fv)) ->
    holding T N cls fields
      (map (fun fv => Held_mk (field_label T cls (fst fv)) (name_of R (snd fv))) fields).
  Proof.
    unfold holding. induction fields as [| fv rest IH]; intros H; cbn; constructor.
    - split; [reflexivity | apply named_all, H; left; reflexivity].
    - apply IH. intros u Hu. apply H. right. exact Hu.
  Qed.

  (** The object at a place, as its event names it, is of the class the naming gives the place. *)
  Lemma placed_named (cls : string) (r : nat) :
    has_name R (vref cls r) -> class_at N r = cls /\ at_place N (name_of R (vref cls r)) r.
  Proof.
    intros H. pose proof (named_all _ H) as Hn. pose proof (ref_class N _ _ _ Hn) as Hc.
    split; [exact Hc |]. unfold at_place. rewrite Hc. exact Hn.
  Qed.

  (** An operation on an object, in a call of the code: its event is the event `Conforms` gives the operation. *)
  Lemma said_event (a : Value) (i : Z) (t : tid) (nxt : nat) (top : call) (σ σ' : state) (X : Type)
      (o : op X) (x : X) :
    is_said o = true -> outside_ top = false -> oprun t nxt o σ = Did x σ' ->
    op_ok T known top σ o x = true -> (forall v, In v (op_vals σ' o x) -> has_name R v) ->
    op_event T known N a i o x (op_said T a i σ' R o x) /\ direct a i (op_said T a i σ' R o x).
  Proof.
    intros Hsaid Hout Hop Hok Hn. destruct o; try discriminate Hsaid; cbn [op_said op_vals op_event] in *.
    - cbn in Hop. destruct (s_obj σ nxt); [discriminate Hop |]. injection Hop as <- <-.
      split; [| split; reflexivity].
      destruct (placed_named cls nxt (Hn _ (or_introl eq_refl))) as [Hc _].
      exists nxt, (name_of R (vref cls nxt)), (map (fun fv => Held_mk (field_label T cls (fst fv)) (name_of R (snd fv))) fields).
      repeat split; try reflexivity; try exact Hc.
      + apply named_all, Hn. left. reflexivity.
      + apply held_all. intros fv Hfv. apply Hn. right. apply in_map. exact Hfv.
    - assert (exists v, x = inr v /\ σ' = σ) as (v & -> & ->).
      { cbn in Hop. crack Hop. eauto. }
      split; [| split; reflexivity].
      destruct (placed_named _ r (Hn _ (or_introl eq_refl))) as [Hc Hat].
      exists v, (name_of R v), (name_of R (vref (class_in σ r) r)). rewrite Hc.
      repeat split; try reflexivity; try exact Hat.
      + apply named_all, Hn. right. left. reflexivity.
      + apply field_typed_b_sound. cbn in Hok. rewrite Hout in Hok. apply andb_true_iff in Hok. apply Hok.
    - assert (x = inr tt) as ->.
      { cbn in Hop. crack Hop. reflexivity. }
      split; [| split; reflexivity].
      destruct (placed_named _ r (Hn _ (or_introl eq_refl))) as [Hc Hat].
      exists (name_of R (vref (class_in σ' r) r)). rewrite Hc. auto.
    - assert (x = inr tt) as ->.
      { cbn in Hop. crack Hop; reflexivity. }
      split; [| split; reflexivity].
      destruct (placed_named _ r (Hn _ (or_introl eq_refl))) as [Hc Hat].
      exists (name_of R (vref (class_in σ' r) r)), (name_of R v). rewrite Hc.
      repeat split; try reflexivity; try exact Hat. apply named_all, Hn. right. left. reflexivity.
    - split; [| split; reflexivity].
      destruct (placed_named _ r (Hn _ (or_introl eq_refl))) as [Hc Hat].
      exists (name_of R (vref (class_in σ' r) r)), (match x with inr (Some v) => Some (name_of R v) | _ => None end).
      rewrite Hc. repeat split; try reflexivity; try exact Hat.
      destruct x as [e | [v |]]; try exact I. apply named_all, Hn. right. left. reflexivity.
  Qed.

  (** ** Where a call is *)

  (** The call made at `i`, among those that wait under `above`: it waits for the one over it. *)
  Fixpoint waiting_in (above : call) (under : list (call * (res -> program))) (i : Z) : stage :=
    match under with
    | [] => Ended
    | (c, k) :: rest =>
        if made c =? i then Waiting (made above) (typed_by known above) k else waiting_in c rest i
    end.

  (** The call a thread made at `i`: running, where it is the thread's top call; waiting, where it is under
      another; ended, where the thread has it no more. *)
  Definition stage_in (th : thread) (i : Z) : stage :=
    match th with
    | Active _ top p under => if made top =? i then Running p else waiting_in top under i
    | Done _ _ => Ended
    end.

  Definition stage_at (c : cfg) (n : nat) (i : Z) : stage :=
    match nth_error (ths c) n with Some th => stage_in th i | None => Ended end.

  (** The calls a thread is in. *)
  Definition frames (th : thread) : list call :=
    match th with Active _ top _ under => top :: map fst under | Done _ _ => [] end.

  (** The thread's call made at `i`, where it has one, is a call of the code: its steps are events. *)
  Definition coded (th : thread) (i : Z) : Prop :=
    forall c, In c (frames th) -> made c = i -> outside_ c = false.

  Lemma waiting_below (above : call) (under : list (call * (res -> program))) (b i : Z) :
    descending b under -> b <= i -> waiting_in above under i = Ended.
  Proof.
    revert above b. induction under as [| [c k] rest IH]; intros above b H Hb; cbn; [reflexivity |].
    destruct H as [Hc Hrest]. destruct (Z.eqb_spec (made c) i); [lia |]. apply (IH c (made c) Hrest). lia.
  Qed.

  (** A call that waits under `above` waits for a call made no later than `above` was. *)
  Lemma waiting_called (above : call) (under : list (call * (res -> program))) (i called : Z) typed k :
    descending (made above) under -> waiting_in above under i = Waiting called typed k -> called <= made above.
  Proof.
    revert above. induction under as [| [c k0] rest IH]; intros above H E; cbn in E; [discriminate E |].
    destruct H as [Hc Hrest]. destruct (made c =? i).
    - injection E as <- _ _. lia.
    - pose proof (IH c Hrest E). lia.
  Qed.

  (** ** One step *)

  (** A step of the thread at the place `n` takes the call that the thread at `m` made at `i`, a call of the
      code, from its stage to the next as `Conforms.takes` says of the step's event, where the event is the
      call's own or the response it waits for; and leaves it where it is otherwise. *)
  Lemma stage_step (w : Z) (n m : nat) (c c' : cfg) (act : action) (i : Z) (th : thread) :
    inv w c -> move T known named w n c act c' ->
    (forall v, In v (mentions act) -> has_name R v) ->
    nth_error (ths c) m = Some th -> has_name R (VTid (tid_of th)) -> coded th i -> i < w ->
    let a := name_of R (VTid (tid_of th)) in
    let e := render T R act in
    (its (stage_at c m i) a i e -> takes T known N a i w e (stage_at c m i) (stage_at c' m i)) /\
    (~ its (stage_at c m i) a i e -> stage_at c' m i = stage_at c m i).
  Proof.
    intros Hinv Hmove Hnames Hm Hown Hcoded Hi a e.
    destruct Hmove as [t top p under th' new Hn Hshape Hrefs Hp Hths Hnext].
    assert (In (Active t top p under) (ths c)) as Hin by (eapply nth_error_In; exact Hn).
    pose proof (inv_stacks w c Hinv _ Hin) as [Htop Hdesc].
    destruct (shape_thread _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hshape (conj Htop Hdesc)) as (_ & _ & Hactor & Hwithin).
    destruct (Nat.eq_dec m n) as [-> | Hmn].
    2: { (* another thread steps: the event is not this call's *)
      assert (stage_at c' m i = stage_at c m i) as Hsame.
      { unfold stage_at. rewrite Hths, (nth_kept _ _ _ _ _ _ Hmn Hm), Hm. reflexivity. }
      assert (~ its (stage_at c m i) a i e) as Hnot.
      { assert (a <> name_of R (VTid (actor act))) as Hne.
        { intros E. pose proof (named_all _ Hown) as H1.
          pose proof (named_all _ (Hnames _ (actor_mentioned act))) as H2.
          fold a in H1. rewrite E in H1. pose proof (names_one N _ _ _ H1 H2) as Et. injection Et as Et.
          rewrite Hactor in Et. pose proof (inv_tids w c Hinv) as Hd.
          apply Hmn. apply (proj1 (NoDup_nth (map tid_of (ths c)) 0%nat) Hd).
          - rewrite length_map. apply nth_error_Some. rewrite Hm. discriminate.
          - rewrite length_map. apply nth_error_Some. rewrite Hn. discriminate.
          - rewrite !(nth_indep _ 0%nat (tid_of th)), !map_nth.
            + rewrite (nth_error_nth _ _ _ Hm), (nth_error_nth _ _ _ Hn). exact Et.
            + rewrite length_map. apply nth_error_Some. rewrite Hn. discriminate.
            + rewrite length_map. apply nth_error_Some. rewrite Hm. discriminate. }
        intros [Hd | Ha].
        - apply Hne. exact (proj1 (direct_render _ _ _ Hd)).
        - destruct (answers_render _ _ _ Ha) as (? & ? & ? & ? & _ & _ & E). exact (Hne E). }
      split; [intros H; destruct (Hnot H) | intros _; exact Hsame]. }
    rewrite Hn in Hm. injection Hm as <-. cbn [tid_of] in a. unfold coded in Hcoded. cbn [frames] in Hcoded.
    assert (stage_at c n i = stage_in (Active t top p under) i) as Hbefore by (unfold stage_at; rewrite Hn; reflexivity).
    assert (stage_at c' n i = stage_in th' i) as Hafter.
    { unfold stage_at. rewrite Hths, (nth_replaced _ _ _ _ _ Hn). reflexivity. }
    rewrite Hbefore, Hafter. clear Hbefore Hafter Hths Hnext Hrefs.
    assert (direct a i e -> made top = i) as Hdir.
    { intros Hd. rewrite <- Hwithin. exact (proj2 (direct_render _ _ _ Hd)). }
    cbn [stage_in]. destruct (Z.eqb_spec (made top) i) as [Etop | Ntop].
    - (* the call is the thread's top call: the step is its own *)
      assert (outside_ top = false) as Hout by (apply Hcoded; [left; reflexivity | exact Etop]).
      destruct Hshape as [x Hs Hans | kd lbl shown act' lp k Hc Hag | X o k x σ1 Hs Hsaid Hop Hok].
      + assert (takes T known N a i w e (Running p)
            (stage_in (match under with [] => Done t x | (c0, k) :: rest => Active t c0 (k x) rest end) i)) as Ht.
        { replace (stage_in _ i) with Ended.
          - eapply takes_end; [exact Hs | subst e; cbn; rewrite Etop; reflexivity |].
            apply gives_response. intros v Hv. apply Hnames. right. exact Hv.
          - destruct under as [| [c0 k0] rest]; [reflexivity |]. cbn. destruct Hdesc as [Hc0 Hrest].
            destruct (Z.eqb_spec (made c0) i); [lia |]. symmetry. apply (waiting_below c0 rest (made c0) i Hrest). lia. }
        split; [intros _; exact Ht |]. intros Hnot. exfalso. apply Hnot. left. subst e. cbn. auto.
      + assert (takes T known N a i w e (Running p)
            (stage_in (Active t (CallOf w kd) lp ((top, k) :: under)) i)) as Ht.
        { cbn [stage_in made]. destruct (Z.eqb_spec w i); [lia |]. cbn [waiting_in].
          destruct (Z.eqb_spec (made top) i); [| contradiction].
          assert (Forall2 (names N) (map (name_of R) shown) shown) as Hys.
          { apply names_map. intros v Hv. apply Hnames. right. exact Hv. }
          subst e. cbn [render]. rewrite Etop. inversion Hc; subst; cbn [typed_by kind_ made].
          - eapply takes_invoke; [eassumption | exact Hys | reflexivity].
          - eapply takes_method; [eassumption | exact Hys | reflexivity].
          - inversion Hys as [| y v ys vs Hy Hrest]; subst.
            eapply takes_function; [eassumption | eassumption | eassumption | exact Hy | exact Hrest | reflexivity]. }
        split; [intros _; exact Ht |]. intros Hnot. exfalso. apply Hnot. left. subst e. cbn. rewrite Etop. auto.
      + rewrite Hout in Hsaid. cbn in Hsaid.
        destruct (said_event a i t (next c) top (heap c) σ1 X o x Hsaid Hout Hop Hok) as [Hev Hd].
        { intros v Hv. apply Hnames. right. exact Hv. }
        cbn [stage_in]. destruct (Z.eqb_spec (made top) i); [| contradiction].
        subst e. cbn [render]. rewrite Etop.
        split; [intros _; eapply takes_op; [exact Hs | exact Hev] | intros Hnot; exfalso; apply Hnot; left; exact Hd].
    - (* the call waits under the top call, or is gone *)
      assert (forall st, its st a i e -> answers st a e) as Hans.
      { intros st [Hd | Ha]; [destruct (Ntop (Hdir Hd)) | exact Ha]. }
      destruct Hshape as [x Hs Hok | kd lbl shown act' lp k Hc Hag | X o k x σ1 Hs Hsaid Hop Hok].
      + destruct under as [| [c0 k0] rest].
        { cbn. split; [intros H; destruct (Hans _ H) | reflexivity]. }
        destruct Hdesc as [Hc0 Hrest]. cbn [waiting_in stage_in].
        destruct (Z.eqb_spec (made c0) i) as [E0 | N0].
        * (* it waits for the top call, which responds *)
          split; [| intros Hnot; exfalso; apply Hnot; right; subst e; cbn; auto].
          intros _. subst e. cbn [render].
          eapply takes_response; [reflexivity | |].
          -- apply gives_response. intros v Hv. apply Hnames. right. exact Hv.
          -- apply typed_ok_sound. cbn in Hok.
             rewrite (Hcoded c0 (or_intror (or_introl eq_refl)) E0) in Hok. exact Hok.
        * (* it waits further down, or is gone: the response is not for it *)
          assert (~ its (waiting_in c0 rest i) a i e) as Hnot.
          { intros H. apply Hans in H. destruct (answers_render _ _ _ H) as (called & typed & k1 & x1 & Est & Eact & _).
            injection Eact as Ecalled _. pose proof (waiting_called c0 rest i called typed k1 Hrest Est). lia. }
          split; [intros H; destruct (Hnot H) | reflexivity].
      + assert (~ its (waiting_in top under i) a i e) as Hnot.
        { intros H. apply Hans in H. destruct (answers_render _ _ _ H) as (? & ? & ? & ? & _ & Eact & _).
          discriminate Eact. }
        split; [intros H; destruct (Hnot H) |]. intros _. cbn [stage_in made waiting_in].
        destruct (Z.eqb_spec w i); [lia |]. destruct (Z.eqb_spec (made top) i); [contradiction | reflexivity].
      + assert (~ its (waiting_in top under i) a i e) as Hnot.
        { intros H. apply Hans in H. destruct (answers_render _ _ _ H) as (? & ? & ? & ? & _ & Eact & _).
          discriminate Eact. }
        split; [intros H; destruct (Hnot H) |]. intros _. cbn [stage_in].
        destruct (Z.eqb_spec (made top) i); [contradiction | reflexivity].
  Qed.

End Stages.
