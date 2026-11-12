(** The forks and the closures Ox makes: what each needs and gives, proven of the code. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps Ox.Inner Ox.HerdProofs.
Import ListNotations.
Open Scope list_scope.

(** ** The code that touches nothing the invariant reads *)

Create HintDb fo.

Ltac fo1 :=
  repeat first
    [ apply fo_retM | apply fo_throw | apply fo_ret
    | apply fo_bind | apply fo_try_catch | apply fo_try_finally
    | apply fo_loop | apply fo_while | apply fo_TsForEach | apply fo_EsForEach | apply fo_VsForEach
    | apply fo_List_foreach | apply fo_extern | apply fo_type_error
    | (apply fo_call; exact I)
    | (apply fo_invokeM; solve [auto])
    | solve [auto with fo]
    | (apply frameonly_neutral; solve [auto with fo])
    | intro
    | match goal with |- neutral _ (match ?x with _ => _ end) => destruct x end ].

Lemma fo_ErrorMode_isError em f : frameonly (ErrorMode_isError em f).
Proof. unfold ErrorMode_isError. fo1. Qed.
Lemma fo_ErrorMode_getError em f : frameonly (ErrorMode_getError em f).
Proof. unfold ErrorMode_getError. fo1. Qed.
Lemma fo_ErrorMode_getT em f : frameonly (ErrorMode_getT em f).
Proof. unfold ErrorMode_getT. fo1. Qed.
Lemma fo_ErrorMode_pure em f : frameonly (ErrorMode_pure em f).
Proof. unfold ErrorMode_pure. fo1. Qed.
Lemma fo_ErrorMode_pureError em f : frameonly (ErrorMode_pureError em f).
Proof. unfold ErrorMode_pureError. fo1. Qed.
Lemma fo_ErrorMode_addSuppressedException em f e : frameonly (ErrorMode_addSuppressedException em f e).
Proof. unfold ErrorMode_addSuppressedException. fo1. Qed.
Lemma fo_ErrorMode_addSuppressedError em f e : frameonly (ErrorMode_addSuppressedError em f e).
Proof. unfold ErrorMode_addSuppressedError. fo1. Qed.
#[export] Hint Resolve fo_ErrorMode_isError fo_ErrorMode_getError fo_ErrorMode_getT fo_ErrorMode_pure
  fo_ErrorMode_pureError fo_ErrorMode_addSuppressedException fo_ErrorMode_addSuppressedError
  fo_isOwnerOrHerdThread fo_assertNotShuttingDown fo_cast_OxError fo_verify : fo.

Lemma fo_cast_option_OxError v : frameonly (cast_option_OxError v).
Proof. unfold cast_option_OxError. fo1. Qed.
Lemma fo_cast_DefaultSupervisor s : frameonly (cast_DefaultSupervisor s).
Proof. unfold cast_DefaultSupervisor. fo1. Qed.
Lemma fo_cast_list v : frameonly (cast_list v).
Proof. unfold cast_list. fo1. Qed.
Lemma fo_currentLocals : frameonly currentLocals.
Proof. unfold currentLocals. fo1. Qed.
Lemma fo_asNoErrorMode x : frameonly (OxError_asNoErrorMode x).
Proof. unfold OxError_asNoErrorMode. fo1. Qed.
#[export] Hint Resolve fo_cast_option_OxError fo_cast_DefaultSupervisor fo_cast_list fo_currentLocals
  fo_asNoErrorMode : fo.

Lemma fo_DefaultSupervisor_new : frameonly DefaultSupervisor_new.
Proof. unfold DefaultSupervisor_new. fo1. Qed.
Lemma fo_DefaultSupervisor_forkStarts s : frameonly (DefaultSupervisor_forkStarts s).
Proof. unfold DefaultSupervisor_forkStarts. fo1. Qed.
Lemma fo_DefaultSupervisor_forkSuccess s : frameonly (DefaultSupervisor_forkSuccess s).
Proof. unfold DefaultSupervisor_forkSuccess. fo1. Qed.
Lemma fo_DefaultSupervisor_forkException s e : frameonly (DefaultSupervisor_forkException s e).
Proof. unfold DefaultSupervisor_forkException. fo1. Qed.
Lemma fo_DefaultSupervisor_forkAppError s e : frameonly (DefaultSupervisor_forkAppError s e).
Proof. unfold DefaultSupervisor_forkAppError. fo1. Qed.
Lemma fo_DefaultSupervisor_join s : frameonly (DefaultSupervisor_join s).
Proof. unfold DefaultSupervisor_join. fo1. Qed.
Lemma fo_DefaultSupervisor_addSuppressedErrors_1 s e : frameonly (DefaultSupervisor_addSuppressedErrors_1 s e).
Proof. unfold DefaultSupervisor_addSuppressedErrors_1. fo1. Qed.
Lemma fo_DefaultSupervisor_addSuppressedErrors_2 s r em : frameonly (DefaultSupervisor_addSuppressedErrors_2 s r em).
Proof. unfold DefaultSupervisor_addSuppressedErrors_2. cbn zeta. fo1. Qed.
#[export] Hint Resolve fo_DefaultSupervisor_new fo_DefaultSupervisor_forkStarts fo_DefaultSupervisor_forkSuccess
  fo_DefaultSupervisor_forkException fo_DefaultSupervisor_forkAppError fo_DefaultSupervisor_join
  fo_DefaultSupervisor_addSuppressedErrors_1 fo_DefaultSupervisor_addSuppressedErrors_2 : fo.

Lemma fo_Supervisor_forkStarts s : frameonly (Supervisor_forkStarts s).
Proof. unfold Supervisor_forkStarts, NoOpSupervisor_forkStarts. fo1. Qed.
Lemma fo_Supervisor_forkSuccess s : frameonly (Supervisor_forkSuccess s).
Proof. unfold Supervisor_forkSuccess, NoOpSupervisor_forkSuccess. fo1. Qed.
Lemma fo_Supervisor_forkException s e : frameonly (Supervisor_forkException s e).
Proof. unfold Supervisor_forkException, NoOpSupervisor_forkException. fo1. Qed.
Lemma fo_Supervisor_forkAppError s e : frameonly (Supervisor_forkAppError s e).
Proof. unfold Supervisor_forkAppError, NoOpSupervisor_forkAppError. fo1. Qed.
Lemma fo_Fork_join f : frameonly (Fork_join f).
Proof. unfold Fork_join. fo1. Qed.
#[export] Hint Resolve fo_Supervisor_forkStarts fo_Supervisor_forkSuccess fo_Supervisor_forkException
  fo_Supervisor_forkAppError fo_Fork_join : fo.

(** ** The closures a fork's thread runs: each calls the closure it wraps and touches nothing else *)

Lemma n_Lam_forkError_1 ox f r arg :
  neutral (fun c a => c = f /\ a = VUnit) (Lam_forkError_1_body ox f r arg).
Proof. unfold Lam_forkError_1_body. cbn zeta. fo1. Qed.

Lemma n_Lam_forkUserError_1 ox f r arg :
  neutral (fun c a => c = f /\ a = VUnit) (Lam_forkUserError_1_body ox f r arg).
Proof. unfold Lam_forkUserError_1_body. cbn zeta. fo1. Qed.

Lemma n_Lam_forkUnsupervised_1 ox f r arg :
  neutral (fun c a => c = f /\ a = VUnit) (Lam_forkUnsupervised_1_body ox f r arg).
Proof. unfold Lam_forkUnsupervised_1_body. cbn zeta. fo1. Qed.

Lemma n_Lam_supervisedError_2 f cap arg :
  neutral (fun c a => c = f /\ a = VObj (O_OxError cap)) (Lam_supervisedError_2_body f cap arg).
Proof. unfold Lam_supervisedError_2_body. fo1. Qed.

(** A closure that calls one closure and touches nothing else leaves the ghost state as its caller left it. *)
Lemma wrapper_ok {A} t Γ0 (f : code) (farg : val) (body : P A) :
  neutral (fun c a => c = f /\ a = farg) body ->
  g_removed Γ0 t = false -> CallPre t f farg Γ0 ->
  wp t body Γ0 (fun _ Γ' => Keep t Γ0 Γ').
Proof.
  intros Hn Hrm Hpre. apply (neutral_wp _ t (fun Γ => Keep t Γ0 Γ) Hn).
  - intros Γ Γ' HK HR. exact (Keep_Rely HK HR).
  - intros Γ HK. rewrite (k_removed HK). exact Hrm.
  - intros c a Γ (-> & ->) HK. split; [exact (CallPre_Keep HK Hpre) |].
    intros Γ' HK'. exact (Keep_trans HK HK').
  - apply Keep_refl.
Qed.

Lemma reaches_Keep {t Γ Γ' h cap} : Keep t Γ Γ' -> reaches Γ t h cap -> reaches Γ' t h cap.
Proof.
  intros HK (Hw & Ha). split; [exact (wf_cap_Ext (k_ext HK) Hw) |].
  destruct Ha as [Ha | (Hi & Hin)]; [left; exact (anc_Ext (k_ext HK) Ha) |].
  right. split; [exact (innermost_Keep HK Hi) | exact (inside_Keep HK Hin)].
Qed.

(** ** The forks: a thread inside a scope's herd starts a fork of it *)

Definition fork_pre (t : tid) (ox : OxError) (f : code) (Γ : gh) : Prop :=
  g_removed Γ t = false /\ knows Γ t ox /\ callable f /\ plain f /\ main_of (hid ox) f /\
  Forall (reaches Γ t (hid ox)) (body_caps f).

Lemma fork_pre_Keep {t ox f Γ Γ'} : Keep t Γ Γ' -> fork_pre t ox f Γ -> fork_pre t ox f Γ'.
Proof.
  intros HK (Hrm & Hk & Hc & Hp & Hm & Hr). split; [rewrite (k_removed HK); exact Hrm |].
  split; [exact (knows_Keep HK Hk) |]. repeat (split; trivial).
  eapply Forall_impl; [| exact Hr]. intros cap H. exact (reaches_Keep HK H).
Qed.

(** What `startThread` is given by each fork. *)
Lemma fork_starts t ox f b Γ0 (Q : exn + unit -> gh -> Prop) :
  fork_pre t ox f Γ0 ->
  callable b -> plain b -> main_of (hid ox) b -> body_caps b = ox :: body_caps f ->
  (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) ->
  wp t (ThreadHerd_startThread (OxError_herd ox) b) Γ0 Q.
Proof.
  intros (Hrm & (Hw & Hin) & Hc & Hp & Hm & Hr) Hcb Hpb Hmb Hcaps HQ.
  apply ThreadHerd_startThread_spec; trivial.
  rewrite Hcaps. constructor; [| exact Hr]. split; [exact Hw | left; constructor].
Qed.

Lemma forkUserError_spec t ox f Γ0 (Q : exn + Fork -> gh -> Prop) :
  fork_pre t ox f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (forkUserError ox f) Γ0 Q.
Proof.
  intros Hpre HQ. unfold forkUserError. cbn zeta.
  pose proof Hpre as (Hrm & _ & Hc & Hp & Hm & _).
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (r & _ & -> & _).
  cbn beta iota.
  pose (K := fun Γ => Keep t Γ0 Γ).
  apply wp_bind. apply (wp_fo t _ Γ1 _ K); [apply fo_Supervisor_forkStarts | | | exact (Rely_Keep HR1) |].
  { intros Γ Γ' HK HR. exact (Keep_Rely HK HR). }
  { intros Γ HK. rewrite (k_removed HK). exact Hrm. }
  intros [e | []] Γ2 HK2; unfold K in HK2; [apply HQ; exact HK2 |].
  apply wp_bind. apply (fork_starts t ox f); cbn; trivial.
  - exact (fork_pre_Keep HK2 Hpre).
  - split; trivial.
  - intros [e | []] Γ3 HK3; apply HQ; exact (Keep_trans HK2 HK3).
Qed.

Lemma forkError_spec t ox f Γ0 (Q : exn + Fork -> gh -> Prop) :
  fork_pre t ox f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (forkError ox f) Γ0 Q.
Proof.
  intros Hpre HQ. unfold forkError. cbn zeta.
  pose proof Hpre as (Hrm & _ & Hc & Hp & Hm & _).
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (r & _ & -> & _).
  cbn beta iota. pose proof (Rely_Keep HR1) as HK1.
  apply wp_bind. apply (fork_starts t ox f); cbn; trivial.
  - exact (fork_pre_Keep HK1 Hpre).
  - split; trivial.
  - intros [e | []] Γ3 HK3; apply HQ; exact (Keep_trans HK1 HK3).
Qed.

Lemma forkUnsupervised_spec t ox f Γ0 (Q : exn + Fork -> gh -> Prop) :
  fork_pre t ox f Γ0 -> (forall r Γ1, Keep t Γ0 Γ1 -> Q r Γ1) -> wp t (forkUnsupervised f ox) Γ0 Q.
Proof.
  intros Hpre HQ. unfold forkUnsupervised. cbn zeta.
  pose proof Hpre as (Hrm & _ & Hc & Hp & Hm & _).
  apply wp_bind. apply wp_frame_res; [exact I | apply can_step_intro; exact Hrm |].
  intros σ1 Γ1 x1 σ1' HI1 HR1 Hs1 Hstep1. cbn in Hstep1. destruct Hstep1 as (r & _ & -> & _).
  cbn beta iota. pose proof (Rely_Keep HR1) as HK1.
  apply wp_bind. apply (fork_starts t ox f); cbn; trivial.
  - exact (fork_pre_Keep HK1 Hpre).
  - split; trivial.
  - intros [e | []] Γ3 HK3; apply HQ; exact (Keep_trans HK1 HK3).
Qed.

(** ** The closure a supervised scope runs on its owner's thread *)

Lemma Lam_supervisedError_1_ok t s em cap f arg Γ0 :
  CallPre t (Lam_supervisedError_1 s em cap f) arg Γ0 ->
  wp t (Lam_supervisedError_1_body s em cap f arg) Γ0 (fun _ Γ' => Keep t Γ0 Γ').
Proof.
  intros (Hc & Hrm & Hk & _ & Hinn). cbn in Hc, Hk, Hinn. unfold Lam_supervisedError_1_body.
  apply Forall_cons_iff in Hk. destruct Hk as (Hkc & Hk). apply Forall_app in Hk. destruct Hk as (Hkf & _).
  pose (K := fun Γ => Keep t Γ0 Γ).
  apply wp_bind. apply forkUserError_spec.
  - split; [exact Hrm |]. split; [exact Hkc |]. split; [exact Hc |]. split; [exact I |].
    split; [reflexivity |]. cbn. constructor.
    + split; [exact (proj1 Hkc) | left; constructor].
    + eapply Forall_impl; [| exact Hkf]. intros c' (Hw & Hi). split; [exact Hw | right; split; trivial].
  - intros [e | fk] Γ1 HK1; [exact HK1 |].
    apply (wp_fo t _ Γ1 _ K); [| | | exact HK1 | intros x Γ2 H2; exact H2].
    + fo1.
    + intros Γ Γ' HK HR. exact (Keep_Rely HK HR).
    + intros Γ HK. rewrite (k_removed HK). exact Hrm.
Qed.
