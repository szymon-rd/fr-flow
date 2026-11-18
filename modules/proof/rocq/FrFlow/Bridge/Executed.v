(** What the machine runs is an execution of the code.

    `machine_conforms`: the events `Frames.execute_frames` gives for a program, read as the event at each moment
    from the first, are an execution of the code in the sense of `Conforms.runs`: the statement every claim of a
    model about the code is proven from. It holds of every table of code, every library of what is outside it,
    every order of the threads' turns and every length of run, and of a run that stops as of one that ends: what
    was run up to there is an execution.

    What it rests on:

    - the machine takes a step only where an execution has one (`Checks`, `Frames`): a run that would take
      another stops there, saying why. That the runs of real programs do not stop so is seen where they are run
      (`OxRunSuite`: the programs give what they give on the JVM);
    - no class of an object of the code with state is named as a variable's is (`no_variable_modules`): decided
      by computing over the table.

    It does not say the machine is the JVM. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library FrFlow.Scala.Run.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Rules.Walk FrFlow.Code.Witness.
Require Import FrFlow.Bridge.Names FrFlow.Bridge.Checks FrFlow.Bridge.Frames FrFlow.Bridge.Steps FrFlow.Bridge.Kept.
Require Import FrFlow.Bridge.Stages FrFlow.Bridge.Bridge.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** ** The naming a run's references give *)

(** The class of the object at a place: that of the first reference to it. *)
Definition place (R : list (Z * val)) (r : nat) : string :=
  match find (fun kv => match snd kv with VObj (Ref _ r') => Nat.eqb r' r | _ => false end) R with
  | Some (_, VObj (Ref c _)) => c
  | _ => ""
  end.

Lemma placed_by (R : list (Z * val)) (σ : state) :
  (forall k cls r, In (k, vref cls r) R -> exists fs, s_obj σ r = Some (cls, fs)) -> placed (place R) R = true.
Proof.
  intros H. unfold placed. apply forallb_forall. intros [k v] Hin. cbn [snd].
  destruct v as [| | | | o | |]; try reflexivity. destruct o as [c r | | | | | | | | |]; try reflexivity.
  unfold place.
  destruct (find (fun kv => match snd kv with VObj (Ref _ r') => Nat.eqb r' r | _ => false end) R)
    as [[k' v'] |] eqn:F.
  - apply find_some in F as [Hin' E]. cbn [snd] in E.
    destruct v' as [| | | | o' | |]; try discriminate E. destruct o' as [c' r' | | | | | | | | |]; try discriminate E.
    apply Nat.eqb_eq in E. subst r'. destruct (H _ _ _ Hin) as [fs Hfs]. destruct (H _ _ _ Hin') as [fs' Hfs'].
    rewrite Hfs in Hfs'. injection Hfs' as -> _. apply String.eqb_refl.
  - pose proof (find_none _ _ F _ Hin) as X. cbn [snd] in X. rewrite Nat.eqb_refl in X. discriminate X.
Qed.

Section Executed.

  Variable files : list tree.
  Variable T : table.
  Variable known : classes.
  Variable named : string -> list val -> option program.

  (** ** Steps one after another are an execution *)

  Theorem trace_conforms (c0 : cfg) (log : list (nat * action)) (cs : list cfg) :
    trace T known named 0 c0 log cs -> inv 0 c0 ->
    (forall r cls fs, s_obj (heap c0) r = Some (cls, fs) -> is_var cls = false) ->
    runs files T known (history T c0 log cs).
  Proof.
    intros Hrun Hinv Hvars.
    pose proof (conf_inv T known named c0 log cs Hrun Hinv (List.length log) (le_n _)) as Hlast.
    pose (N := naming_of (R c0 log cs) (place (R c0 log cs)) (good_named _ (inv_good _ _ Hlast))
      (placed_by _ _ (inv_placed _ _ Hlast))).
    assert (forall v, has_name (R c0 log cs) v -> names N (name_of (R c0 log cs) v) v) as Hall.
    { intros v. apply name_of_names. }
    exists N. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    - exact (run_method_calls T known named c0 log cs Hrun Hinv N Hall).
    - exact (run_module_calls T known named c0 log cs Hrun Hinv N Hall).
    - exact (run_function_calls files T known named c0 log cs Hrun Hinv N Hall).
    - exact (run_never_atomic files T known c0 log cs N).
    - exact (run_made_once T known named c0 log cs Hrun Hinv N Hall).
    - exact (run_answered_once T known named c0 log cs Hrun Hinv N Hall).
    - exact (run_constructor_calls T known named c0 log cs Hrun Hinv N Hall).
    - exact (run_variables_hold T known named c0 log cs Hrun Hinv N Hall Hvars).
  Qed.

  (** ** What `run_frames` gives is such steps *)

  Lemma trace_length w c log cs : trace T known named w c log cs -> List.length cs = S (List.length log).
  Proof. induction 1; cbn; [reflexivity | congruence]. Qed.

  Lemma trace_grows w c log cs :
    trace T known named w c log cs -> exists more, refs (nth (List.length log) cs c) = refs c ++ more.
  Proof.
    induction 1 as [w c | w c n act c1 log cs Hm Htr IH].
    - exists []. cbn. rewrite app_nil_r. reflexivity.
    - destruct IH as [more E]. destruct Hm as [t top p under th' new _ _ Hrefs _ _ _].
      destruct (extend_more (refs c) (mentions act)) as [more' E']. rewrite Hrefs, E' in E.
      exists (more' ++ more). cbn [List.length nth]. rewrite app_assoc, <- E. f_equal. apply nth_indep.
      rewrite (trace_length _ _ _ _ Htr). lia.
  Qed.

  Lemma run_trace (order : nat -> nat) (fuel : nat) :
    forall ths σ rs nxt turn idle past v es R',
      run_frames T known named order fuel ths σ rs nxt turn idle past = (v, es, R') ->
      exists log cs,
        trace T known named (Z.of_nat (List.length past)) (Cfg ths σ rs nxt) log cs /\
        refs (nth (List.length log) cs (Cfg ths σ rs nxt)) = R' /\
        es = rev past ++ map (fun na => render T R' (snd na)) log.
  Proof.
    assert (forall ths σ rs nxt past (v v' : verdict) es R',
      (v', rev past, rs) = (v, es, R') ->
      exists log cs,
        trace T known named (Z.of_nat (List.length past)) (Cfg ths σ rs nxt) log cs /\
        refs (nth (List.length log) cs (Cfg ths σ rs nxt)) = R' /\
        es = rev past ++ map (fun na => render T R' (snd na)) log) as Hover.
    { intros ths σ rs nxt past v v' es R' E. injection E as _ <- <-. exists [], [Cfg ths σ rs nxt].
      split; [constructor | split; [reflexivity | cbn; rewrite app_nil_r; reflexivity]]. }
    induction fuel as [| fuel IH]; intros ths σ rs nxt turn idle past v es R' H; cbn [run_frames] in H.
    { exact (Hover _ _ _ _ _ _ _ _ _ H). }
    destruct (alive_at ths 0) as [| a alive] eqn:Ealive; [exact (Hover _ _ _ _ _ _ _ _ _ H) |].
    destruct (Nat.leb (List.length (a :: alive)) idle); [exact (Hover _ _ _ _ _ _ _ _ _ H) |].
    destruct (nth_error (a :: alive) (Nat.modulo (order turn + idle) (List.length (a :: alive)))) as [[i t] |];
      [| exact (Hover _ _ _ _ _ _ _ _ _ H)].
    destruct (nth_error ths i) as [th |] eqn:Ei; [| exact (Hover _ _ _ _ _ _ _ _ _ H)].
    destruct (step_thread T known named (Z.of_nat (List.length past)) nxt σ rs th) as [th' σ' rs' new e | |] eqn:St;
      [| exact (IH _ _ _ _ _ _ _ _ _ _ H) | exact (Hover _ _ _ _ _ _ _ _ _ H)].
    destruct th as [t0 top p under | t0 x]; [| discriminate St].
    destruct (step_shape T known named _ _ _ _ _ _ _ _ _ _ _ _ _ St) as (act & Hshape & Hrs & Hplaced & He).
    destruct (IH _ _ _ _ _ _ _ _ _ _ H) as (log & cs & Htr & Hlast & Hes).
    set (c := Cfg ths σ rs nxt). set (c1 := Cfg (firstn i ths ++ th' :: skipn (S i) ths ++ new) σ' rs' (S nxt)) in *.
    exists ((i, act) :: log), (c :: cs). split; [| split].
    - apply (trace_step T known named _ c i act c1); [exact (moved T known named _ i c act c1 _ _ _ _ _ _ Ei Hshape Hrs Hplaced eq_refl eq_refl) |].
      replace (Z.of_nat (List.length past) + 1) with (Z.of_nat (List.length (e :: past))) by (cbn [List.length]; lia).
      exact Htr.
    - cbn [List.length nth]. rewrite <- Hlast. f_equal. apply nth_indep. rewrite (trace_length _ _ _ _ Htr). lia.
    - rewrite Hes. cbn [rev map snd]. rewrite <- app_assoc. cbn [app]. do 2 f_equal.
      destruct (trace_grows _ _ _ _ Htr) as [more Hmore]. rewrite Hlast in Hmore. cbn [refs c1] in Hmore.
      rewrite He, Hmore. symmetry. apply render_more. intros u Hu. rewrite Hrs. apply extend_names. exact Hu.
  Qed.

  (** ** A program run *)

  (** No object of the code with state is of a class named as a variable's is. *)
  Definition no_variable_modules : bool := forallb (fun c => negb (is_var c)) (stateful_modules T).

  Theorem machine_conforms (order : nat -> nat) (fuel : nat) (main : sym) v es R' :
    no_variable_modules = true ->
    execute_frames T known named order fuel main = (v, es, R') -> runs files T known (history_of es).
  Proof.
    intros Hmods H. unfold execute_frames in H.
    destruct (run_trace order fuel _ _ _ _ _ _ _ _ _ _ H) as (log & cs & Htr & Hlast & Hes).
    set (c0 := Cfg [first_thread T main] (state0 T (Method main)) [] (S (List.length (stateful_modules T)))) in *.
    cbn [List.length rev app] in Htr, Hes.
    assert (R c0 log cs = R') as ER.
    { unfold R, conf. rewrite Nat.min_id. exact Hlast. }
    replace (history_of es) with (history T c0 log cs) by (unfold history; rewrite ER, Hes; reflexivity).
    apply (trace_conforms c0 log cs Htr).
    - split.
      + lia.
      + intros th [<- | []]. cbn. split; [lia | exact I].
      + cbn. repeat constructor. intros [].
      + intros th [<- | []]. eexists. split; [reflexivity | discriminate].
      + apply good_nil.
      + intros k cls r [].
    - intros r cls fs Hr. cbn in Hr. destruct r as [| r]; [discriminate Hr |].
      destruct (nth_error (stateful_modules T) r) as [c |] eqn:E; [| discriminate Hr]. injection Hr as <- _.
      unfold no_variable_modules in Hmods. rewrite forallb_forall in Hmods.
      apply negb_true_iff. apply Hmods. eapply nth_error_In. exact E.
  Qed.

End Executed.
