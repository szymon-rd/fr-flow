(** Proving what threads keep: an invariant, ghost state, and a rule for each kind of step.

    The proof of a program is given with: a ghost state (`Gh`: what the proof records beside the JDK's state), an
    invariant relating the two (`Inv`), and for each thread what the steps of the other threads may do to the
    ghost state (`Rely`). A thread knows the ghost state as it last left it and that the others have since kept
    to `Rely`; at each operation it shows that, whatever the JDK's contract lets the operation do, there is a
    ghost state the invariant holds of again, which the other threads' `Rely` admits.

    `wp t p Γ Q`: thread `t`, running `p`, having left the ghost state at `Γ`, keeps the invariant at every
    step, and if `p` ends, `Q` holds of its result and the ghost state then. It says nothing of whether `p` ends.

    `sound`: when the first thread's program and every closure meet `wp`, the invariant holds in every state the
    threads reach, by every order of their steps. *)

From Stdlib Require Import ZArith List Bool.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem.

Set Implicit Arguments.

Section Logic.

  Variables code obj : Type.
  Abbreviation jst := (jst code obj).
  Abbreviation P := (P code obj).
  Abbreviation res := (res code obj).
  Variable interp : code -> P res.

  Variable Gh : Type.
  Variable Inv : jst -> Gh -> Prop.
  Variable Rely : tid -> Gh -> Gh -> Prop.
  Hypothesis Rely_refl : forall t Γ, Rely t Γ Γ.
  Hypothesis Rely_trans : forall t Γ1 Γ2 Γ3, Rely t Γ1 Γ2 -> Rely t Γ2 Γ3 -> Rely t Γ1 Γ3.

  (** What a step of thread `t` may do to the ghost state: what every other thread's `Rely` admits. *)
  Definition Guar (t : tid) (Γ Γ' : Gh) : Prop := forall u, u <> t -> Rely u Γ Γ'.

  (** A closure called: what the caller owes, and what it has when the call returns. *)
  Variable CallPre : tid -> code -> Gh -> Prop.
  Variable CallPost : tid -> code -> Gh -> res -> Gh -> Prop.
  (** A closure started as a thread: what the starter owes, and what holds when the thread ends. *)
  Variable StartPre : tid -> code -> Gh -> Prop.
  Variable Done : tid -> res -> Gh -> Prop.

  Fixpoint wp (A : Type) (t : tid) (p : P A) (Γ0 : Gh) (Q : A -> Gh -> Prop) {struct p} : Prop :=
    match p with
    | Ret a => Q a Γ0
    | Vis o k =>
        forall σ Γ, Inv σ Γ -> Rely t Γ0 Γ -> started σ t ->
        forall x σ', opstep t o σ x σ' ->
        exists Γ', Inv σ' Γ' /\ Guar t Γ Γ' /\
          (forall u c, u <> t -> starts σ σ' u c -> StartPre u c Γ') /\
          wp t (k x) Γ' Q
    | Iter body s k =>
        exists J, J s Γ0 /\
          forall s1 Γ1, J s1 Γ1 ->
            wp t (body s1) Γ1 (fun r Γ2 => match r with inl s2 => J s2 Γ2 | inr b => wp t (k b) Γ2 Q end)
    | Call c k =>
        CallPre t c Γ0 /\ forall r Γ1, CallPost t c Γ0 r Γ1 -> wp t (k r) Γ1 Q
    end.

  Lemma wp_mono (A : Type) (p : P A) : forall t Γ0 (Q Q' : A -> Gh -> Prop),
    (forall a Γ, Q a Γ -> Q' a Γ) -> wp t p Γ0 Q -> wp t p Γ0 Q'.
  Proof.
    induction p as [A a | A X o k IH | A S B body IHb s k IHk | A c k IH]; intros t Γ0 Q Q' HQ; cbn.
    - apply HQ.
    - intros H σ Γ HI HR Hs x σ' Hstep.
      destruct (H σ Γ HI HR Hs x σ' Hstep) as (Γ' & HI' & HG & Hst & Hk).
      exists Γ'. repeat split; trivial. eapply IH; eassumption.
    - intros (J & HJ & Hbody). exists J. split; trivial.
      intros s1 Γ1 HJ1. eapply IHb; [| apply Hbody, HJ1].
      intros [s2 | b] Γ2; cbn; trivial. apply IHk, HQ.
    - intros (Hpre & Hk). split; trivial. intros r Γ1 Hpost. eapply IH; [exact HQ | apply Hk, Hpost].
  Qed.

  Lemma wp_bind (A : Type) (p : P A) : forall (B : Type) (f : A -> P B) t Γ0 (Q : B -> Gh -> Prop),
    wp t p Γ0 (fun a Γ1 => wp t (f a) Γ1 Q) -> wp t (pbind p f) Γ0 Q.
  Proof.
    induction p as [A a | A X o k IH | A S B body IHb s k IHk | A c k IH]; intros B' f t Γ0 Q; cbn.
    - trivial.
    - intros H σ Γ HI HR Hs x σ' Hstep.
      destruct (H σ Γ HI HR Hs x σ' Hstep) as (Γ' & HI' & HG & Hst & Hk).
      exists Γ'. repeat split; trivial. apply IH, Hk.
    - intros (J & HJ & Hbody). exists J. split; trivial.
      intros s1 Γ1 HJ1. eapply wp_mono; [| apply Hbody, HJ1].
      intros [s2 | b] Γ2; cbn; trivial. apply IHk.
    - intros (Hpre & Hk). split; trivial. intros r Γ1 Hpost. apply IH, Hk, Hpost.
  Qed.

  (** ** Soundness *)

  (** Every closure meets what is said of it. *)
  Hypothesis call_ok : forall t c Γ, CallPre t c Γ -> wp t (interp c) Γ (CallPost t c Γ).
  Hypothesis start_ok : forall u c Γ, StartPre u c Γ -> wp u (interp c) Γ (Done u).
  (** A thread's end keeps the invariant. *)
  Hypothesis exit_ok : forall σ Γ t r Γt, Inv σ Γ -> Rely t Γt Γ -> started σ t -> Done t r Γt ->
    exists Γ', Inv (terminate σ t) Γ' /\ Guar t Γ Γ'.

  (** What holds of every configuration the threads reach. *)
  Definition good (c : config code obj) : Prop :=
    exists Γ, Inv (c_st c) Γ /\
      forall t p, c_pool c t = Some p ->
        started (c_st c) t /\ exists Γt, Rely t Γt Γ /\ wp t p Γt (Done t).

  Lemma started_clear_intr (σ : jst) t u : started σ u -> started (clear_intr σ t) u.
  Proof.
    unfold started, clear_intr. destruct (j_th σ t) as [[c s i] |] eqn:E; trivial.
    cbn. unfold upd. destruct (Nat.eq_dec u t) as [-> |]; trivial. rewrite E. trivial.
  Qed.

  Lemma started_set_th (σ : jst) v th u :
    (started σ v -> t_status th = TStarted) -> started σ u -> started (set_th σ v th) u.
  Proof.
    unfold started. cbn. unfold upd. intros Hv. destruct (Nat.eq_dec u v) as [-> |]; trivial.
    intro Hs. specialize (Hv Hs). destruct th as [c s i]. cbn in Hv. subst. trivial.
  Qed.

  Ltac unpack :=
    repeat match goal with
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | H : _ \/ _ |- _ => destruct H
      end; subst; trivial.

  (** No operation ends a thread or takes one back to before its start. *)
  Lemma opstep_started t X (o : op code obj X) σ x σ' u :
    opstep t o σ x σ' -> started σ u -> started σ' u.
  Proof.
    destruct o; cbn; intros H Hu; unpack; try (apply started_clear_intr; assumption).
    - (* NewThread *)
      apply started_set_th; trivial. unfold started. rewrite H. contradiction.
    - (* ThreadStart *)
      destruct (j_th σ u0) as [[c s i] |] eqn:E; [destruct s |]; unpack.
      apply started_set_th; trivial.
    - (* ThreadInterrupt *)
      destruct (j_th σ u0) as [[c s i] |] eqn:E; [destruct s |]; unpack;
        apply started_set_th; trivial; unfold started; rewrite E; contradiction.
    - (* CfComplete *)
      destruct (j_cf σ r) as [[? |] |]; unpack; contradiction.
    - (* CfCompleteExceptionally *)
      destruct (j_cf σ r) as [[? |] |]; unpack; contradiction.
    - (* ArUpdateAndGet *)
      destruct (f x0); unpack.
  Qed.

  Theorem sound_step c c' : good c -> step interp c c' -> good c'.
  Proof.
    intros (Γ & HI & Hpool) Hstep.
    destruct Hstep as [σ pl t X o k x σ' pl' Ht Hop Hpt Hkeep Hnew Hstart
                      | σ pl t S B body s k Ht | σ pl t c k Ht | σ pl t r Ht]; cbn in *.
    - (* an operation *)
      destruct (Hpool t _ Ht) as (Hs & Γt & HR & Hwp). cbn in Hwp.
      destruct (Hwp σ Γ HI HR Hs x σ' Hop) as (Γ' & HI' & HG & Hst & Hk).
      exists Γ'. split; trivial. cbn. intros u p Hu.
      destruct (Nat.eq_dec u t) as [-> | Hne].
      + rewrite Hpt in Hu. injection Hu as <-. split; [eapply opstep_started; eassumption |].
        exists Γ'. split; [apply Rely_refl | exact Hk].
      + destruct (started_dec σ u) as [Hsu | Hnsu].
        * rewrite (Hkeep u Hne Hsu) in Hu. destruct (Hpool u p Hu) as (_ & Γu & HRu & Hwpu).
          split; [eapply opstep_started; eassumption |].
          exists Γu. split; [eapply Rely_trans; [exact HRu | apply HG, Hne] | exact Hwpu].
        * destruct (started_dec σ' u) as [Hsu' | Hnsu'].
          -- assert (Hc : exists c, starts σ σ' u c).
             { unfold starts, started in *. destruct (j_th σ' u) as [[c' s' i'] |]; try contradiction.
               destruct s'; try contradiction. exists c'. split; trivial. }
             destruct Hc as (c & Hc). rewrite (Hstart u c Hne Hc) in Hu. injection Hu as <-.
             split; trivial. exists Γ'. split; [apply Rely_refl | apply start_ok, Hst; assumption].
          -- rewrite (Hnew u Hne Hnsu Hnsu') in Hu. destruct (Hpool u p Hu) as (Hsu & _). contradiction.
    - (* a turn of a loop *)
      exists Γ. split; trivial. cbn. intros u p Hu. unfold upd in Hu.
      destruct (Nat.eq_dec u t) as [-> | Hne]; [| apply Hpool, Hu].
      injection Hu as <-. destruct (Hpool t _ Ht) as (Hs & Γt & HR & Hwp). split; trivial.
      exists Γt. split; trivial. cbn in Hwp. destruct Hwp as (J & HJ & Hbody).
      unfold unfold_iter. apply wp_bind. eapply wp_mono; [| apply Hbody, HJ].
      intros [s2 | b] Γ2; cbn; trivial. intro HJ2. exists J. split; trivial.
    - (* a call *)
      exists Γ. split; trivial. cbn. intros u p Hu. unfold upd in Hu.
      destruct (Nat.eq_dec u t) as [-> | Hne]; [| apply Hpool, Hu].
      injection Hu as <-. destruct (Hpool t _ Ht) as (Hs & Γt & HR & Hwp). split; trivial.
      exists Γt. split; trivial. cbn in Hwp. destruct Hwp as (Hpre & Hk).
      apply wp_bind. eapply wp_mono; [| apply call_ok, Hpre]. exact Hk.
    - (* a thread's end *)
      destruct (Hpool t _ Ht) as (Hs & Γt & HR & Hwp). cbn in Hwp.
      destruct (exit_ok HI HR Hs Hwp) as (Γ' & HI' & HG).
      exists Γ'. split; trivial. cbn. intros u p Hu. unfold upd in Hu.
      destruct (Nat.eq_dec u t) as [-> | Hne]; [discriminate |].
      destruct (Hpool u p Hu) as (Hsu & Γu & HRu & Hwpu). split.
      + unfold started, terminate in *. destruct (j_th σ t) as [th |] eqn:E; trivial.
        cbn. unfold upd. destruct (Nat.eq_dec u t); [contradiction | trivial].
      + exists Γu. split; [eapply Rely_trans; [exact HRu | apply HG, Hne] | exact Hwpu].
  Qed.

  Theorem sound c c' : good c -> steps interp c c' -> good c'.
  Proof. intros Hg Hs. induction Hs as [| c c' c'' _ IH Hstep]; trivial. eapply sound_step; [apply IH, Hg | exact Hstep]. Qed.

End Logic.
