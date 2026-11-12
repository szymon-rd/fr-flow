(** The forks and the closures Ox makes: what each needs and gives, proven of the code. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Code Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps Ox.Inner Ox.HerdProofs.
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
