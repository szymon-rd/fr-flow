(** Operations that touch nothing the invariant reads, and programs made of them.

    The invariant reads the JDK's state through the sets of threads, the references of finalizers, and each
    thread's closure and place in its life. An operation that leaves those as they were keeps the invariant with
    the ghost state unchanged. A program built from such operations alone keeps whatever the thread knew. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Code Ox.Ghost Ox.Facts Ox.Specs.
Import ListNotations.
Open Scope list_scope.

Definition same_view (σ σ' : jst) : Prop :=
  j_ts σ' = j_ts σ /\ j_ar σ' = j_ar σ /\
  forall u, match j_th σ u, j_th σ' u with
            | Some (Thread c s _), Some (Thread c' s' _) => c' = c /\ s' = s
            | None, None => True
            | _, _ => False
            end.

Lemma sv_refl σ : same_view σ σ.
Proof. repeat split. intro u. destruct (j_th σ u) as [[c s i] |]; auto. Qed.

Lemma sv_fwd {σ σ' u c s i} : same_view σ σ' -> j_th σ u = Some (Thread c s i) ->
  exists i', j_th σ' u = Some (Thread c s i').
Proof.
  intros (_ & _ & H) E. specialize (H u). rewrite E in H.
  destruct (j_th σ' u) as [[c' s' i'] |]; [| contradiction]. destruct H as [-> ->]. eauto.
Qed.

Lemma sv_bwd {σ σ' u c s i} : same_view σ σ' -> j_th σ' u = Some (Thread c s i) ->
  exists i', j_th σ u = Some (Thread c s i').
Proof.
  intros (_ & _ & H) E. specialize (H u). rewrite E in H.
  destruct (j_th σ u) as [[c' s' i'] |]; [| contradiction]. destruct H as [-> ->]. eauto.
Qed.

Lemma sv_none {σ σ' u} : same_view σ σ' -> j_th σ' u = None -> j_th σ u = None.
Proof.
  intros (_ & _ & H) E. specialize (H u). rewrite E in H.
  destruct (j_th σ u) as [[c' s' i'] |]; [contradiction | trivial].
Qed.

Lemma sv_begun {σ σ' u} : same_view σ σ' -> begun σ' u -> begun σ u.
Proof.
  intros Hsv. unfold begun. destruct (j_th σ' u) as [[c s i] |] eqn:E; [| contradiction].
  destruct (sv_bwd Hsv E) as (i' & ->). trivial.
Qed.

Lemma sv_started {σ σ' u} : same_view σ σ' -> started σ' u -> started σ u.
Proof.
  intros Hsv. unfold started. destruct (j_th σ' u) as [[c s i] |] eqn:E; [| contradiction].
  destruct (sv_bwd Hsv E) as (i' & ->). trivial.
Qed.

Lemma inv_frame {σ σ' Γ} : Inv σ Γ -> same_view σ σ' -> Inv σ' Γ.
Proof.
  intros HI Hsv. pose proof Hsv as (Hts & Har & _).
  constructor.
  - intros h hr H. rewrite Hts. exact (i_herd HI H).
  - intros h hr H Hx u b Hr. exact (i_exit HI H Hx Hr).
  - intros u h. exact (i_open HI u h).
  - intro u. exact (i_nodup HI u).
  - intros u pre h post hr H1 H2. exact (i_stack HI H1 H2).
  - intros h hr h1 H1 H2. exact (i_stamp HI H1 H2).
  - intros h hr H. exact (i_clock HI H).
  - intros u H. exact (i_removed HI H).
  - intros u Hn. apply (i_new HI). intro Hb. apply Hn. unfold begun in *.
    destruct (j_th σ u) as [[c s i] |] eqn:E; [| contradiction].
    destruct (sv_fwd Hsv E) as (i' & ->). trivial.
  - intros u Hn. apply (i_none HI). exact (sv_none Hsv Hn).
  - intros u t th b Hr. destruct (i_created HI Hr) as (i & E). exact (sv_fwd Hsv E).
  - intros u h b Hr. destruct (i_fork HI Hr) as (Hreg & th & st & i & E & Hth). split; trivial.
    destruct (sv_fwd Hsv E) as (i' & E'). eauto.
  - intros u Hb. apply (i_started HI). exact (sv_begun Hsv Hb).
  - intros u H. exact (i_main HI H).
  - intros r H. rewrite Har. exact (i_fin HI H).
  - intros (c & i & E). apply (i_done HI). destruct (sv_bwd Hsv E) as (i' & E'). eauto.
Qed.

(** The operations that leave the view as it was. *)
Definition frame_op {X : Type} (o : Jdk.op code obj X) : Prop :=
  match o with
  | NewThread _ | ThreadStart _ | TsNew | TsAdd _ _ | TsRemove _ _
  | ArNew _ | ArGetAndSet _ _ | ArUpdateAndGet _ _ | Chaos _ _ => False
  | _ => True
  end.

Lemma sv_set_th {σ u c s i} i' : j_th σ u = Some (Thread c s i) -> same_view σ (set_th σ u (Thread c s i')).
Proof.
  intro E. repeat split. intro v. cbn. unfold upd. destruct (Nat.eq_dec v u) as [-> |].
  - rewrite E. auto.
  - destruct (j_th σ v) as [[c' s' i''] |]; auto.
Qed.

Lemma sv_clear_intr σ t : same_view σ (clear_intr σ t).
Proof.
  unfold clear_intr. destruct (j_th σ t) as [[c s i] |] eqn:E; [| apply sv_refl].
  cbn. exact (sv_set_th false E).
Qed.

Ltac unpack :=
  repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    end; subst.

Lemma sv_same_th σ σ' : j_ts σ' = j_ts σ -> j_ar σ' = j_ar σ -> j_th σ' = j_th σ -> same_view σ σ'.
Proof.
  intros A B C. repeat split; trivial. intro u. rewrite C. destruct (j_th σ u) as [[c s i] |]; auto.
Qed.

Lemma opstep_frame {t X} {o : Jdk.op code obj X} {σ x σ'} : frame_op o -> opstep t o σ x σ' -> same_view σ σ'.
Proof.
  destruct o; cbn; intros Hf H; try contradiction; unpack;
    try apply sv_refl; try apply sv_clear_intr; try (apply sv_same_th; reflexivity).
  - (* ThreadInterrupt *)
    destruct (j_th σ u) as [[c s i] |] eqn:E; [destruct s |]; unpack;
      try apply sv_refl; exact (sv_set_th true E).
  - (* CfComplete *)
    destruct (j_cf σ r) as [[? |] |]; unpack; try contradiction; try apply sv_refl.
    apply sv_same_th; reflexivity.
  - (* CfCompleteExceptionally *)
    destruct (j_cf σ r) as [[? |] |]; unpack; try contradiction; try apply sv_refl.
    apply sv_same_th; reflexivity.
Qed.

Lemma sv_no_starts {σ σ' u c} : same_view σ σ' -> ~ starts σ σ' u c.
Proof.
  intros Hsv (Hn & Hs). apply Hn. apply (sv_started Hsv). unfold started.
  destruct (j_th σ' u) as [[c' s' i'] |]; [destruct s' |]; trivial.
Qed.

(** ** Rules for operations that keep the view *)

(** What a thread knows stays under the steps of others. *)
Definition stable (t : tid) (Pst : gh -> Prop) : Prop := forall Γ Γ', Pst Γ -> Rely t Γ Γ' -> Pst Γ'.

Lemma wp_frame X t (o : Jdk.op code obj (exn + X)) Γ0 (Q : exn + X -> gh -> Prop) :
  frame_op o -> can_step t Γ0 -> (forall x Γ, Rely t Γ0 Γ -> Q x Γ) -> wp t (call o) Γ0 Q.
Proof.
  intros Hf Hc HQ. unfold call, wp. cbn. intros σ Γ HI HR Hs. split; [eapply Hc; eauto |].
  intros x σ' Hstep. pose proof (opstep_frame Hf Hstep) as Hsv.
  exists Γ. split; [eapply inv_frame; eauto |]. split; [intros u _; apply Rely_refl |].
  split; [| apply HQ, HR].
  intros u c _ Hst. exfalso. eapply sv_no_starts; eauto.
Qed.

(** ** Programs of such operations alone *)

Inductive frameonly : forall A : Type, P A -> Prop :=
  | fo_ret A (a : A) : frameonly A (Ret a)
  | fo_vis A X (o : Jdk.op code obj X) (k : X -> P A) :
      frame_op o -> (forall x, frameonly A (k x)) -> frameonly A (Vis o k)
  | fo_iter A S B (body : S -> P (S + B)) (s : S) (k : B -> P A) :
      (forall s1, frameonly (S + B) (body s1)) -> (forall b, frameonly A (k b)) -> frameonly A (Iter body s k).

Arguments frameonly {A} p.

Theorem frameonly_wp {A} {p : P A} t (Pst : gh -> Prop) :
  frameonly p -> stable t Pst -> (forall Γ, Pst Γ -> g_removed Γ t = false) ->
  forall Γ, Pst Γ -> wp t p Γ (fun _ Γ' => Pst Γ').
Proof.
  intros Hfo Hst Hact. induction Hfo as [A a | A X o k Hf _ IH | A S B body s k _ IHb _ IHk]; intros Γ HP.
  - exact HP.
  - unfold wp. cbn. intros σ Γ1 HI HR Hs.
    assert (HP1 : Pst Γ1) by (eapply Hst; eauto).
    split; [unfold Active; auto |].
    intros x σ' Hstep. pose proof (opstep_frame Hf Hstep) as Hsv.
    exists Γ1. split; [eapply inv_frame; eauto |]. split; [intros u _; apply Rely_refl |].
    split; [| apply IH, HP1].
    intros u c _ Hstt. exfalso. eapply sv_no_starts; eauto.
  - unfold wp. cbn. exists (fun _ Γ1 => Pst Γ1). split; trivial.
    intros s1 Γ1 HP1. split.
    + intros σ Γ2 _ HR _. unfold Active. apply Hact. eapply Hst; eauto.
    + eapply Logic.wp_mono; [| apply IHb, HP1].
      intros [s2 | b] Γ2 HP2; cbn; trivial. apply IHk, HP2.
Qed.

Lemma fo_pbind A B (p : P A) (f : A -> P B) :
  frameonly p -> (forall a, frameonly (f a)) -> frameonly (pbind p f).
Proof.
  intros Hp Hf. induction Hp as [A a | A X o k Ho _ IH | A S C body s k Hb _ _ IHk]; cbn.
  - apply Hf.
  - apply fo_vis; trivial. intro x. apply IH, Hf.
  - apply fo_iter; trivial. intro b. apply IHk, Hf.
Qed.

Lemma fo_bind A B (m : M A) (f : A -> M B) :
  frameonly m -> (forall a, frameonly (f a)) -> frameonly (bind m f).
Proof. intros Hm Hf. apply fo_pbind; trivial. intros [e | a]; [apply fo_ret | apply Hf]. Qed.

Lemma fo_retM A (a : A) : frameonly (ret (code := code) (obj := obj) a).
Proof. apply fo_ret. Qed.

Lemma fo_throw A e : frameonly (throw (code := code) (obj := obj) (A := A) e).
Proof. apply fo_ret. Qed.

Lemma fo_call X (o : Jdk.op code obj (exn + X)) : frame_op o -> frameonly (call o).
Proof. intro H. apply fo_vis; trivial. intro x. apply fo_ret. Qed.

Lemma fo_try_catch A (m : M A) (h : exn -> M A) :
  frameonly m -> (forall e, frameonly (h e)) -> frameonly (try_catch m h).
Proof. intros Hm Hh. apply fo_pbind; trivial. intros [e | a]; [apply Hh | apply fo_ret]. Qed.

Lemma fo_try_finally A (m : M A) (fin : M unit) :
  frameonly m -> frameonly fin -> frameonly (try_finally m fin).
Proof.
  intros Hm Hf. apply fo_pbind; trivial. intro r. apply fo_pbind; trivial.
  intros [e | []]; apply fo_ret.
Qed.

Lemma fo_loop S B (body : S -> M (S + B)) (s : S) :
  (forall s1, frameonly (body s1)) -> frameonly (loop body s).
Proof.
  intro Hb. apply fo_iter; [| intro; apply fo_ret]. intro s1. apply fo_pbind; [apply Hb |].
  intros [e | [s2 | b]]; apply fo_ret.
Qed.

Lemma fo_while S (cond : S -> M bool) (body : S -> M S) (s : S) :
  (forall s1, frameonly (cond s1)) -> (forall s1, frameonly (body s1)) -> frameonly (while cond body s).
Proof.
  intros Hc Hb. apply fo_loop. intro s1. apply fo_bind; [apply Hc |].
  intros [|]; [apply fo_bind; [apply Hb | intro; apply fo_ret] | apply fo_ret].
Qed.

Lemma fo_TsForEach S (r : nat) (f : tid -> S -> M S) (s : S) :
  (forall u s1, frameonly (f u s1)) -> frameonly (TsForEach r f s).
Proof.
  intro Hf. apply fo_loop. intros [seen s1]. apply fo_bind; [apply fo_call; exact I |].
  intros [u |]; [apply fo_bind; [apply Hf | intro; apply fo_ret] | apply fo_ret].
Qed.

Lemma fo_EsForEach S (r : nat) (f : exn -> S -> M S) (s : S) :
  (forall u s1, frameonly (f u s1)) -> frameonly (EsForEach r f s).
Proof.
  intro Hf. apply fo_loop. intros [seen s1]. apply fo_bind; [apply fo_call; exact I |].
  intros [u |]; [apply fo_bind; [apply Hf | intro; apply fo_ret] | apply fo_ret].
Qed.

Lemma fo_VsForEach S (r : nat) (f : val -> S -> M S) (s : S) :
  (forall u s1, frameonly (f u s1)) -> frameonly (VsForEach r f s).
Proof.
  intro Hf. apply fo_loop. intros [seen s1]. apply fo_bind; [apply fo_call; exact I |].
  intros [u |]; [apply fo_bind; [apply Hf | intro; apply fo_ret] | apply fo_ret].
Qed.

Lemma fo_List_foreach A (xs : list A) (f : A -> M unit) :
  (forall x, frameonly (f x)) -> frameonly (List_foreach xs f).
Proof.
  intro Hf. induction xs as [| x xs IH]; cbn; [apply fo_ret |].
  apply fo_bind; [apply Hf | intro; exact IH].
Qed.

Lemma fo_extern A name : frameonly (extern (code := code) (obj := obj) (A := A) name).
Proof. apply fo_call. exact I. Qed.

Lemma fo_type_error A : frameonly (type_error (code := code) (obj := obj) (A := A)).
Proof. apply fo_vis; [exact I | intro; apply fo_ret]. Qed.
