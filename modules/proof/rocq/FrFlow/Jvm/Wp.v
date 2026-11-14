(** A logic for programs of the machine, in Iris.

    What the logic knows of the machine's state (`jvm_interp`): each object of the program and each object of a
    class from outside is owned (`r ↦obj o`, `r ↦ext h`), by a thread or by an invariant several share; a thread
    made and not started is owned by whoever may start it, a running thread owns itself; that a thread was
    started, and that it has ended, are facts that stay (`started u`, `ended u`); and the state has not gone
    wrong.

    `wpP t p E Φ`: thread `t` running the program `p` keeps every invariant, does not go wrong, and if `p` ends
    with `a` then `Φ a` holds. It says nothing of whether `p` ends. It is Iris's weakest precondition of the
    thread, said of a part of its program by what the rest may assume. *)

From Stdlib Require Import FunctionalExtensionality.
From iris.algebra Require Import gmap.
From iris.base_logic.lib Require Export ghost_map invariants.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import lifting.
From iris.proofmode Require Import proofmode.
From FrFlow.Threads Require Import Prog.
From FrFlow.Jvm Require Export Lang.

(** ** Programs *)

Section prog.
  Context {Op : Type → Type} {code V R : Type}.

  Lemma pbind_ret {A} (p : prog Op code V R A) : pbind p Ret = p.
  Proof.
    induction p as [a | X o k IH | S B body IHb s k IH | c arg k IH]; simpl; [done | | |];
      f_equal; apply functional_extensionality; done.
  Qed.

  Lemma pbind_assoc {A B C} (p : prog Op code V R A) (f : A → prog Op code V R B) (g : B → prog Op code V R C) :
    pbind (pbind p f) g = pbind p (λ a, pbind (f a) g).
  Proof.
    induction p as [a | X o k IH | S B' body IHb s k IH | c arg k IH]; simpl; [done | | |];
      f_equal; apply functional_extensionality; done.
  Qed.

  Lemma unfold_iter_bind {S B C} (body : S → prog Op code V R (S + B)) s (k : B → prog Op code V R C) :
    pbind (unfold_iter body s Ret) k = unfold_iter body s k.
  Proof.
    unfold unfold_iter. rewrite pbind_assoc. f_equal. apply functional_extensionality. by intros [s' | b].
  Qed.
End prog.

(** ** What the logic owns *)

Class jvmGpreS (code obj : Type) (Σ : gFunctors) := JvmGpreS {
  #[global] jvm_pre_inv :: invGpreS Σ;
  #[global] jvm_pre_obj :: ghost_mapG Σ nat (Machine.object code obj);
  #[global] jvm_pre_ext :: ghost_mapG Σ nat (Machine.held code obj);
  #[global] jvm_pre_th :: ghost_mapG Σ tid (code * tstatus);
  #[global] jvm_pre_set :: ghost_mapG Σ tid unit }.

Class jvmGS (code obj : Type) (Σ : gFunctors) := JvmGS {
  #[global] jvm_inv :: invGS Σ;
  #[global] jvm_objG :: ghost_mapG Σ nat (Machine.object code obj);
  #[global] jvm_extG :: ghost_mapG Σ nat (Machine.held code obj);
  #[global] jvm_thG :: ghost_mapG Σ tid (code * tstatus);
  #[global] jvm_setG :: ghost_mapG Σ tid unit;
  jvm_obj : gname;
  jvm_ext : gname;
  jvm_th : gname;
  jvm_started : gname;
  jvm_ended : gname;
  jvm_new : gname }.

(** An object of the program at `r`, and one of a class from outside: who owns it may change it; a part of it
    (`{dq}`) lets it be read; `□` is a part that is everyone's for good, of an object that no longer changes. *)
Definition obj_at `{!jvmGS code obj Σ} (r : nat) (dq : dfrac) (o : Machine.object code obj) : iProp Σ :=
  ghost_map_elem jvm_obj r dq o.
Definition ext_at `{!jvmGS code obj Σ} (r : nat) (dq : dfrac) (h : Machine.held code obj) : iProp Σ :=
  ghost_map_elem jvm_ext r dq h.

Notation "r ↦obj dq o" := (obj_at r dq o)
  (at level 20, dq custom dfrac at level 1, format "r  ↦obj dq  o") : bi_scope.
Notation "r ↦ext dq h" := (ext_at r dq h)
  (at level 20, dq custom dfrac at level 1, format "r  ↦ext dq  h") : bi_scope.

Section owned.
  Context `{!jvmGS code obj Σ}.
  Global Instance obj_at_timeless r dq o : Timeless (r ↦obj{dq} o).
  Proof. apply _. Qed.
  Global Instance obj_at_persistent r o : Persistent (r ↦obj□ o).
  Proof. apply _. Qed.
  Global Instance ext_at_timeless r dq h : Timeless (r ↦ext{dq} h).
  Proof. apply _. Qed.
  Global Instance ext_at_persistent r h : Persistent (r ↦ext□ h).
  Proof. apply _. Qed.

  Lemma obj_at_persist r dq o : r ↦obj{dq} o ==∗ r ↦obj□ o.
  Proof. apply ghost_map_elem_persist. Qed.
  Lemma obj_at_agree r dq1 dq2 o1 o2 : r ↦obj{dq1} o1 -∗ r ↦obj{dq2} o2 -∗ ⌜o1 = o2⌝.
  Proof. apply ghost_map_elem_agree. Qed.
  Lemma ext_at_agree r dq1 dq2 h1 h2 : r ↦ext{dq1} h1 -∗ r ↦ext{dq2} h2 -∗ ⌜h1 = h2⌝.
  Proof. apply ghost_map_elem_agree. Qed.
End owned.

Section logic.
  Context {code obj : Type} `{!jvmGS code obj Σ}.
  Context (interp : code → Machine.val code obj → Machine.P code obj (Machine.res code obj)).

  Abbreviation mval := (Machine.val code obj).
  Abbreviation mstate := (Machine.state code obj).
  Abbreviation prog := (Machine.P code obj).
  Abbreviation mres := (Machine.res code obj).
  Abbreviation thread := (running code obj).

  (** A thread, with what it runs and where it is in its life: who holds it may move it on. *)
  Definition thread_is (u : tid) (c : code) (s : tstatus) : iProp Σ :=
    ghost_map_elem jvm_th u (DfracOwn 1) (c, s).
  (** The thread was made: there is one of this for each thread, given to who made it. *)
  Definition made (u : tid) : iProp Σ := ghost_map_elem jvm_new u (DfracOwn 1) ().
  (** The thread was started. *)
  Definition started (u : tid) : iProp Σ := ghost_map_elem jvm_started u DfracDiscarded ().
  (** The thread has ended. *)
  Definition ended (u : tid) : iProp Σ := ghost_map_elem jvm_ended u DfracDiscarded ().

  Global Instance started_persistent u : Persistent (started u).
  Proof. apply _. Qed.
  Global Instance ended_persistent u : Persistent (ended u).
  Proof. apply _. Qed.
  Global Instance started_timeless u : Timeless (started u).
  Proof. apply _. Qed.
  Global Instance ended_timeless u : Timeless (ended u).
  Proof. apply _. Qed.

  Global Instance made_timeless u : Timeless (made u).
  Proof. apply _. Qed.

  (** A thread is made once. *)
  Lemma made_once u : made u -∗ made u -∗ False.
  Proof. iIntros "H1 H2". iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _]. done. Qed.

  Definition status_of (th : option (Machine.thread code)) : option (code * tstatus) :=
    match th with Some th => Some (t_code th, t_status th) | None => None end.

  Definition begun (σ : mstate) (u : tid) : Prop :=
    match s_th σ u with Some (Thread _ TNew _) | None => False | _ => True end.
  Definition over (σ : mstate) (u : tid) : Prop :=
    match s_th σ u with Some (Thread _ TTerminated _) => True | _ => False end.

  Definition jvm_interp (σ : mstate) : iProp Σ :=
    ∃ (mo : gmap nat (Machine.object code obj)) (me : gmap nat (Machine.held code obj))
      (mt : gmap tid (code * tstatus)) (ms mz mn : gmap tid unit),
      ghost_map_auth jvm_obj (DfracOwn 1) mo ∗ ghost_map_auth jvm_ext (DfracOwn 1) me ∗
      ghost_map_auth jvm_th (DfracOwn 1) mt ∗
      ghost_map_auth jvm_started (DfracOwn 1) ms ∗ ghost_map_auth jvm_ended (DfracOwn 1) mz ∗
      ghost_map_auth jvm_new (DfracOwn 1) mn ∗
      ([∗ map] u ↦ _ ∈ mz, ended u) ∗
      ⌜(∀ r, mo !! r = s_obj σ r) ∧ (∀ r, me !! r = s_ext σ r) ∧ (∀ u, mt !! u = status_of (s_th σ u)) ∧
       (∀ u, is_Some (ms !! u) → begun σ u) ∧ (∀ u, is_Some (mz !! u) ↔ over σ u) ∧ s_wrong σ = None ∧
       (∀ u, is_Some (mn !! u) → s_th σ u ≠ None)⌝.

  (** Iris's weakest precondition, of this machine with this account of its state. It is no instance outside
      a section that fixes `interp`: there it is declared for that `interp`. *)
  Local Instance jvm_irisGS : irisGS (jvm interp) Σ := {
    iris_invGS := jvm_inv;
    state_interp σ _ _ _ := jvm_interp σ;
    fork_post _ := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _ }.

  (** ** A program of a thread *)

  Definition wpP {A : Type} (t : tid) (p : prog A) (E : coPset) (Φ : A → iProp Σ) : iProp Σ :=
    ∀ (k : A → prog mres) (Ψ : final → iProp Σ),
      (∀ a, Φ a -∗ WP (Running t (k a) : thread) @ MaybeStuck; E {{ Ψ }}) -∗
      WP (Running t (pbind p k) : thread) @ MaybeStuck; E {{ Ψ }}.

  Lemma wpP_ret {A} t (a : A) E Φ : Φ a ⊢ wpP t (Ret a) E Φ.
  Proof. iIntros "H" (k Ψ) "K". by iApply "K". Qed.

  Lemma wpP_bind {A B} t (p : prog A) (f : A → prog B) E Φ :
    wpP t p E (λ a, wpP t (f a) E Φ) ⊢ wpP t (pbind p f) E Φ.
  Proof.
    iIntros "H" (k Ψ) "K". rewrite pbind_assoc. iApply "H". iIntros (a) "Hf". by iApply "Hf".
  Qed.

  Lemma wpP_wand {A} t (p : prog A) E Φ Φ' :
    wpP t p E Φ -∗ (∀ a, Φ a -∗ Φ' a) -∗ wpP t p E Φ'.
  Proof. iIntros "H W" (k Ψ) "K". iApply "H". iIntros (a) "Ha". iApply "K". by iApply "W". Qed.

  Lemma wpP_fupd {A} t (p : prog A) E Φ : (|={E}=> wpP t p E Φ) ⊢ wpP t p E Φ.
  Proof. iIntros "H" (k Ψ) "K". iMod "H". by iApply "H". Qed.

  Lemma wpP_post_fupd {A} t (p : prog A) E Φ : wpP t p E (λ a, |={E}=> Φ a) ⊢ wpP t p E Φ.
  Proof. iIntros "H" (k Ψ) "K". iApply "H". iIntros (a) ">Ha". by iApply "K". Qed.

  Lemma wpP_frame {A} t (p : prog A) E Φ R : R -∗ wpP t p E Φ -∗ wpP t p E (λ a, R ∗ Φ a).
  Proof. iIntros "R H". iApply (wpP_wand with "H"). iIntros (a) "$". done. Qed.

  (** A step that touches no state: one turn of a loop, a call of a closure. Each gives a later. *)
  Lemma wp_pure_step t (p p' : prog mres) E Ψ :
    (∀ σ e' σ' started, Machine.step interp (Running t p) σ e' σ' started →
       e' = Running t p' ∧ σ' = σ ∧ started = []) →
    ▷ WP (Running t p' : thread) @ MaybeStuck; E {{ Ψ }} ⊢ WP (Running t p : thread) @ MaybeStuck; E {{ Ψ }}.
  Proof.
    iIntros (Hstep) "H". iApply wp_lift_step; [done |].
    iIntros (σ ns κs nt) "Hσ". iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose".
    iSplit; [done |]. iIntros "!>" (e2 σ2 efs κ κs' -> [_ Hs]) "_".
    destruct (Hstep _ _ _ _ Hs) as (-> & -> & ->). iMod "Hclose" as "_". iModIntro. simpl. iFrame.
  Qed.

  Lemma wpP_call t c arg E Φ : ▷ wpP t (interp c arg) E Φ ⊢ wpP t (Call c arg Ret) E Φ.
  Proof.
    iIntros "H" (k Ψ) "K". simpl. iApply wp_pure_step; [by intros ???? (-> & -> & ->) |].
    iNext. iApply "H". done.
  Qed.

  Lemma wpP_iter {S B} t (body : S → prog (S + B)) s E Φ :
    ▷ wpP t (unfold_iter body s Ret) E Φ ⊢ wpP t (Iter body s Ret) E Φ.
  Proof.
    iIntros "H" (k Ψ) "K".
    iApply (wp_pure_step t _ (unfold_iter body s k)); [by intros ???? (-> & -> & ->) |].
    iNext. rewrite -(unfold_iter_bind body s k). by iApply "H".
  Qed.

  (** An operation: whatever the machine lets it do, the logic's account of the state is made good again, each
      thread it started is given what it needs, and what follows has what it needs. *)
  Lemma wpP_op {X} t (o : Machine.op code obj X) E Φ :
    (∀ σ, jvm_interp σ ={E,∅}=∗ ▷ ∀ x σ', ⌜opstep t o σ x σ'⌝ ={∅,E}=∗
       jvm_interp σ' ∗ ([∗ list] e ∈ forked interp σ o, WP (e : thread) @ MaybeStuck; ⊤ {{ _, True }}) ∗ Φ x)
    ⊢ wpP t (Vis o Ret) E Φ.
  Proof.
    iIntros "H" (k Ψ) "K". simpl. iApply wp_lift_step; [done |].
    iIntros (σ ns κs nt) "Hσ". iMod ("H" with "Hσ") as "H". iModIntro.
    iSplit; [done |]. iIntros "!>" (e2 σ2 efs κ κs' -> [_ (x & Hop & -> & ->)]) "_".
    iMod ("H" $! x σ2 with "[//]") as "($ & $ & HΦ)". iModIntro. by iApply "K".
  Qed.

End logic.
