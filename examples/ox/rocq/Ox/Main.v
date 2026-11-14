(** Containment: when the first thread has ended, no other thread has an operation left.

    For every client whose closures keep to what is asked of them (`client_ok`), in every configuration the
    threads reach from the first thread running a closure of the client, by any order of their steps. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps Ox.Inner Ox.HerdProofs
  Ox.ScopeProofs.
Import ListNotations.
Open Scope list_scope.

(** A herd its closing loop has left has an empty set, in the JDK's own state, and it stays exited: so does
    every scope that has completed, at any depth, not only the first thread's. *)
Theorem exited_empty σ Γ h hr :
  Inv σ Γ -> g_herd Γ h = Some hr -> h_exited hr = true ->
  exists s, j_ts σ h = Some s /\ forall u, s u = false.
Proof.
  intros HI Hh Hx. destruct (i_herd HI Hh) as (s & Hs & Hiff). exists s. split; [exact Hs |].
  intro u. destruct (s u) eqn:E; trivial. apply Hiff in E. destruct E as ((b & Hb) & Hrm).
  rewrite (i_exit HI Hh Hx Hb) in Hrm. discriminate.
Qed.

Section Main.

  (** The client's closures: any programs. *)
  Variable client : nat -> list OxError -> val -> M val.

  (** What is asked of the client: each of its closures, called by a thread that is inside the herd of every
      capability the closure holds or is given, leaves the ghost state as its caller left it. *)
  Hypothesis client_ok : forall t n caps arg Γ, CallPre t (Client n caps) arg Γ ->
    wp t (client n caps arg) Γ (fun _ Γ' => Keep t Γ Γ').

  (** A closure a fork wraps may be called by the fork's thread. *)
  Lemma pre_wrapped t f ox arg Γ :
    callable f -> g_removed Γ t = false -> Forall (knows Γ t) (ox :: body_caps f ++ arg_caps arg) ->
    extra t f Γ -> CallPre t f VUnit Γ.
  Proof.
    intros Hc Hrm Hk He. apply Forall_cons_iff in Hk. destruct Hk as (_ & Hk).
    apply Forall_app in Hk. destruct Hk as (Hkf & _).
    split; [exact Hc |]. split; [exact Hrm |]. split; [rewrite app_nil_r; exact Hkf |].
    split; [intros cap E; discriminate | exact He].
  Qed.

  Lemma call_ok t c arg Γ : CallPre t c arg Γ -> wp t (interp client c arg) Γ (CallPost t c arg Γ).
  Proof.
    intros Hpre. pose proof Hpre as (Hc & Hrm & Hk & Ha & He).
    destruct c as [th b | ox f r | ox f r | ox f r | s em cap f | f cap | n caps]; cbn [interp].
    - contradiction.
    - apply (wrapper_ok t Γ f VUnit); [apply n_Lam_forkError_1 | exact Hrm |].
      destruct Hc as (Hc & _). exact (pre_wrapped t f ox arg Γ Hc Hrm Hk He).
    - apply (wrapper_ok t Γ f VUnit); [apply n_Lam_forkUserError_1 | exact Hrm |].
      destruct Hc as (Hc & _). exact (pre_wrapped t f ox arg Γ Hc Hrm Hk He).
    - apply (wrapper_ok t Γ f VUnit); [apply n_Lam_forkUnsupervised_1 | exact Hrm |].
      destruct Hc as (Hc & _). exact (pre_wrapped t f ox arg Γ Hc Hrm Hk He).
    - apply Lam_supervisedError_1_ok. exact Hpre.
    - apply (wrapper_ok t Γ f (VObj (O_OxError cap))); [apply n_Lam_supervisedError_2 | exact Hrm |].
      cbn in Hc, Hk, He. apply Forall_cons_iff in Hk. destruct Hk as (Hkc & Hk).
      apply Forall_app in Hk. destruct Hk as (Hkf & _).
      split; [destruct f; cbn in Hc; trivial; contradiction |]. split; [exact Hrm |].
      split; [apply Forall_app; split; [exact Hkf | cbn; constructor; [exact Hkc | constructor]] |].
      split; [intros cap' E; injection E as <-; exact He |].
      destruct f; cbn in Hc; trivial; contradiction.
    - apply client_ok. exact Hpre.
  Qed.

  Lemma start_ok u c Γ : StartPre u c Γ -> wp u (interp client c VUnit) Γ (Done u).
  Proof.
    intros Hpre. destruct c; cbn in Hpre; try contradiction. cbn [interp]. apply runnable_spec. exact Hpre.
  Qed.

  Lemma exit_ok σ Γ t (r : res) Γt :
    Inv σ Γ -> Rely t Γt Γ -> started σ t -> Done t r Γt ->
    exists Γ', Inv (terminate σ t) Γ' /\ Logic.Guar Rely t Γ Γ'.
  Proof.
    intros HI HR Hs Hd. exists Γ. split; [| intros u _; apply Rely_refl].
    apply inv_terminate; trivial. rewrite (r_open HR). exact Hd.
  Qed.

  (** A thread with a step left that is not its end has not taken itself out. *)
  Lemma wp_active {A} t (p : P A) Γt (Q : A -> gh -> Prop) σ Γ :
    wp t p Γt Q -> Inv σ Γ -> Rely t Γt Γ -> started σ t -> (forall a, p <> Ret a) -> Active t Γ.
  Proof.
    intros Hw HI HR Hs Hnr. unfold wp in Hw. destruct p as [a | X o k | S B body s k | c arg k]; cbn in Hw.
    - exfalso. exact (Hnr a eq_refl).
    - destruct (Hw σ Γ HI HR Hs) as (Ha & _). exact Ha.
    - destruct Hw as (J & HJ & Hb). destruct (Hb s Γt HJ) as (Hc & _). exact (Hc σ Γ HI HR Hs).
    - destruct Hw as (Hc & _). exact (Hc σ Γ HI HR Hs).
  Qed.

  (** ** The start *)

  Definition σ0 (c0 : code) : jst :=
    Jst (fun u => if Nat.eq_dec u main then Some (Thread c0 TStarted false) else None)
        (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None)
        (fun _ => None) (fun _ _ => None) (fun _ => None) (fun _ => None).

  Definition Γinit : gh :=
    mkG (fun _ => None) (fun u => if Nat.eq_dec u main then Main else NoRole) (fun _ => false)
        (fun _ => []) (fun _ => false) 0.

  (** The first thread runs a closure of the client's that holds no capability. *)
  Definition init (n0 : nat) : config code obj :=
    Config (σ0 (Client n0 []))
           (fun u => if Nat.eq_dec u main then Some (interp client (Client n0 []) VUnit) else None).

  Lemma inv_init c0 : Inv (σ0 c0) Γinit.
  Proof.
    constructor; cbn.
    - intros h hr H. discriminate.
    - intros h hr H. discriminate.
    - intros u h. split; [intros [] | intros (hr & H & _); discriminate].
    - intro u. constructor.
    - intros u pre h post hr H. destruct pre; discriminate.
    - intros h hr h1 H. discriminate.
    - intros h hr H. discriminate.
    - intros u H. discriminate.
    - intros u _. auto.
    - intros u H. destruct (Nat.eq_dec u main); [discriminate | trivial].
    - intros u t th b H. destruct (Nat.eq_dec u main); discriminate.
    - intros u h b H. destruct (Nat.eq_dec u main); discriminate.
    - intros u H. unfold begun in H. cbn in H. destruct (Nat.eq_dec u main); [auto | contradiction].
    - intros u H. destruct (Nat.eq_dec u main); [trivial | discriminate].
    - intros r H. discriminate.
    - intros (c & i & E). destruct (Nat.eq_dec main main); [discriminate | contradiction].
  Qed.

  Definition good : config code obj -> Prop :=
    Logic.good Inv Rely Active CallPre CallPost StartPre Done.

  Lemma good_init n0 : good (init n0).
  Proof.
    exists Γinit. split; [apply inv_init |]. cbn. intros t p Hp.
    destruct (Nat.eq_dec t main) as [-> |]; [| discriminate]. injection Hp as <-.
    split.
    - unfold started. cbn. destruct (Nat.eq_dec main main); [exact I | contradiction].
    - exists Γinit. split; [apply Rely_refl |].
      change (wp main (client n0 [] VUnit) Γinit (Done main)).
      apply wp_mono with (Q := fun _ Γ' => Keep main Γinit Γ').
      + intros r Γ HK. unfold Done. rewrite (k_open HK). reflexivity.
      + apply client_ok. split; [exact I |]. split; [reflexivity |]. split; [constructor |].
        split; [intros cap E; discriminate | exact I].
  Qed.

  Theorem reached_good n0 c : steps (interp client) (init n0) c -> good c.
  Proof.
    intro Hs. unfold good.
    exact (Logic.sound Rely_refl Rely_trans call_ok start_ok exit_ok (good_init n0) Hs).
  Qed.

  (** ** The theorem *)

  Theorem contained n0 c :
    steps (interp client) (init n0) c ->
    (exists code0 i, j_th (c_st c) main = Some (Thread code0 TTerminated i)) ->
    forall u p, c_pool c u = Some p -> exists r, p = Ret r.
  Proof.
    intros Hsteps Hend u p Hp.
    destruct (reached_good n0 c Hsteps) as (Γ & HI & Hpool).
    destruct (Hpool u p Hp) as (Hs & Γu & HR & Hw).
    pose proof (i_done HI Hend) as Hmain.
    destruct p as [a | X o k | S B body s k | c0 arg k]; [eauto | | |]; exfalso.
    all: assert (Hact : Active u Γ) by (eapply wp_active; eauto; intros a E; discriminate).
    all: unfold Active in Hact.
    all: assert (Hb : begun (c_st c) u) by (apply begun_started; exact Hs).
    all: destruct (i_started HI Hb) as [Hm | (h & b & Hr)].
    all: try (rewrite (all_removed _ _ HI Hmain u h b Hr) in Hact; discriminate).
    all: apply (i_main HI) in Hm; subst u; destruct Hend as (code0 & i & E);
      unfold started in Hs; rewrite E in Hs; exact Hs.
  Qed.

End Main.
