(** What is said of each closure, and the rules of proof specialised to Ox's invariant. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Code Ox.Ghost Ox.Facts.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Abbreviation res := (Sem.res code obj).
Abbreviation P := (Sem.P code obj).

(** The herd of a capability, by the reference of its set of threads. *)
Definition hid (cap : OxError) : nat := ThreadHerd_threads (OxError_herd cap).

Definition wf_herd (Γ : gh) (th : ThreadHerd) : Prop :=
  exists hr, g_herd Γ (ThreadHerd_threads th) = Some hr /\ h_owner hr = ThreadHerd_herdOwner th.

Definition wf_cap (Γ : gh) (cap : OxError) : Prop :=
  wf_herd Γ (OxError_herd cap) /\ g_fin Γ (OxError_finalizers cap) = true.

(** The capabilities a closure holds. *)
Fixpoint body_caps (c : code) : list OxError :=
  match c with
  | Lam_ThreadHerd_startThread_1 _ t => body_caps t
  | Lam_forkError_1 ox f _ => ox :: body_caps f
  | Lam_forkUserError_1 ox f _ => ox :: body_caps f
  | Lam_forkUnsupervised_1 ox f _ => ox :: body_caps f
  | Lam_supervisedError_1 _ _ cap f => cap :: body_caps f
  | Lam_supervisedError_2 f cap => cap :: body_caps f
  | Client _ caps => caps
  end.

(** A closure that is called, not started as a thread. *)
Fixpoint callable (c : code) : Prop :=
  match c with
  | Lam_ThreadHerd_startThread_1 _ _ => False
  | Lam_forkError_1 _ f _ => callable f
  | Lam_forkUserError_1 _ f _ => callable f
  | Lam_forkUnsupervised_1 _ f _ => callable f
  | Lam_supervisedError_1 _ _ _ f => callable f
  | Lam_supervisedError_2 f _ => callable f
  | Client _ _ => True
  end.

(** A closure that may be a fork's body: any but the one a supervised scope runs on its owner's thread. *)
Definition plain (c : code) : Prop :=
  match c with Lam_supervisedError_1 _ _ _ _ => False | _ => True end.

Definition arg_caps (v : val) : list OxError :=
  match v with VObj (O_OxError cap) => [cap] | _ => [] end.

(** The herd a thread is most deeply inside: the innermost it owns open, or else the one it is a fork of. *)
Definition innermost (Γ : gh) (t : tid) (h : nat) : Prop :=
  match g_open Γ t with
  | h' :: _ => h' = h
  | [] => (exists b, g_role Γ t = ForkOf h b) /\ g_removed Γ t = false
  end.

(** A thread may use a capability: it is well formed and the thread is inside its herd. *)
Definition knows (Γ : gh) (t : tid) (cap : OxError) : Prop := wf_cap Γ cap /\ inside Γ t (hid cap).

(** What a call leaves of the ghost state, as its caller sees it. *)
Record Keep (t : tid) (Γ Γ' : gh) : Prop := {
  k_ext : Ext Γ Γ';
  k_removed : g_removed Γ' t = g_removed Γ t;
  k_open : g_open Γ' t = g_open Γ t }.

Lemma Keep_refl t Γ : Keep t Γ Γ.
Proof. constructor; trivial. apply Ext_refl. Qed.

Lemma Keep_trans t Γ1 Γ2 Γ3 : Keep t Γ1 Γ2 -> Keep t Γ2 Γ3 -> Keep t Γ1 Γ3.
Proof. intros [A B C] [A' B' C']. constructor; [eapply Ext_trans; eauto | congruence | congruence]. Qed.

Lemma Rely_Keep t Γ Γ' : Rely t Γ Γ' -> Keep t Γ Γ'.
Proof. intro H. constructor; [eapply Rely_Ext; eauto | apply (r_removed H) | apply (r_open H)]. Qed.

(** ** The closures *)

Definition CallPre (t : tid) (c : code) (arg : val) (Γ : gh) : Prop :=
  callable c /\ g_removed Γ t = false /\ Forall (knows Γ t) (body_caps c ++ arg_caps arg) /\
  (forall cap, arg = VObj (O_OxError cap) -> innermost Γ t (hid cap)) /\
  match c with Lam_supervisedError_1 _ _ cap _ => innermost Γ t (hid cap) | _ => True end.

Definition CallPost (t : tid) (c : code) (arg : val) (Γ : gh) (r : res) (Γ' : gh) : Prop := Keep t Γ Γ'.

(** A fork's thread: it is in its herd's set, has done nothing, and its body may run in that herd. *)
Definition StartPre (u : tid) (c : code) (Γ : gh) : Prop :=
  match c with
  | Lam_ThreadHerd_startThread_1 th b =>
      (exists b', g_role Γ u = ForkOf (ThreadHerd_threads th) b') /\ g_removed Γ u = false /\
      g_open Γ u = [] /\ callable b /\ plain b /\
      Forall (fun cap => wf_cap Γ cap /\ anc Γ (ThreadHerd_threads th) (hid cap)) (body_caps b)
  | _ => False
  end.

(** A thread ends owning no open herd. *)
Definition Done (u : tid) (r : res) (Γ : gh) : Prop := g_open Γ u = [].

Definition wp {A : Type} (t : tid) (p : P A) (Γ : gh) (Q : A -> gh -> Prop) : Prop :=
  Logic.wp Inv Rely Active CallPre CallPost StartPre t p Γ Q.

(** A thread that has not taken itself out may step: what `wp` asks before each step. *)
Definition can_step (t : tid) (Γ0 : gh) : Prop :=
  forall σ Γ, Inv σ Γ -> Rely t Γ0 Γ -> started σ t -> Active t Γ.

Lemma can_step_intro t Γ0 : g_removed Γ0 t = false -> can_step t Γ0.
Proof. intros H σ Γ _ HR _. unfold Active. rewrite (r_removed HR). trivial. Qed.

(** ** The rules, for programs that may throw *)

Lemma wp_mono A t (p : P A) Γ (Q Q' : A -> gh -> Prop) :
  (forall a Γ1, Q a Γ1 -> Q' a Γ1) -> wp t p Γ Q -> wp t p Γ Q'.
Proof. apply Logic.wp_mono. Qed.

Lemma wp_ret A t (a : A) Γ (Q : exn + A -> gh -> Prop) : Q (inr a) Γ -> wp t (ret a) Γ Q.
Proof. trivial. Qed.

Lemma wp_throw A t e Γ (Q : exn + A -> gh -> Prop) : Q (inl e) Γ -> wp t (throw e) Γ Q.
Proof. trivial. Qed.

Lemma wp_bind A B t (m : M A) (f : A -> M B) Γ (Q : exn + B -> gh -> Prop) :
  wp t m Γ (fun r Γ1 => match r with inl e => Q (inl e) Γ1 | inr a => wp t (f a) Γ1 Q end) ->
  wp t (bind m f) Γ Q.
Proof.
  intro H. unfold bind, wp. apply Logic.wp_bind. eapply Logic.wp_mono; [| exact H].
  intros [e | a] Γ1; trivial.
Qed.

Lemma wp_try_catch A t (m : M A) (h : exn -> M A) Γ (Q : exn + A -> gh -> Prop) :
  wp t m Γ (fun r Γ1 => match r with inl e => wp t (h e) Γ1 Q | inr a => Q (inr a) Γ1 end) ->
  wp t (try_catch m h) Γ Q.
Proof.
  intro H. unfold try_catch, wp. apply Logic.wp_bind. eapply Logic.wp_mono; [| exact H].
  intros [e | a] Γ1; trivial.
Qed.

Lemma wp_try_finally A t (m : M A) (fin : M unit) Γ (Q : exn + A -> gh -> Prop) :
  wp t m Γ (fun r Γ1 => wp t fin Γ1 (fun r2 Γ2 =>
    match r2 with inl e => Q (inl e) Γ2 | inr _ => Q r Γ2 end)) ->
  wp t (try_finally m fin) Γ Q.
Proof.
  intro H. unfold try_finally, wp. apply Logic.wp_bind. eapply Logic.wp_mono; [| exact H].
  intros r Γ1 H1. apply Logic.wp_bind. eapply Logic.wp_mono; [| exact H1].
  intros [e | []] Γ2; trivial.
Qed.

Lemma wp_loop S B t (body : S -> M (S + B)) (s : S) Γ (Q : exn + B -> gh -> Prop) (J : S -> gh -> Prop) :
  J s Γ ->
  (forall s1 Γ1, J s1 Γ1 -> can_step t Γ1 /\
     wp t (body s1) Γ1 (fun r Γ2 => match r with
       | inl e => Q (inl e) Γ2
       | inr (inl s2) => J s2 Γ2
       | inr (inr b) => Q (inr b) Γ2
       end)) ->
  wp t (loop body s) Γ Q.
Proof.
  intros HJ Hbody. unfold loop, wp. cbn. exists J. split; trivial.
  intros s1 Γ1 HJ1. destruct (Hbody s1 Γ1 HJ1) as (Hc & Hw). split; [exact Hc |].
  apply Logic.wp_bind. eapply Logic.wp_mono; [| exact Hw].
  intros [e | [s2 | b]] Γ2; trivial.
Qed.

Lemma wp_invoke t c arg Γ (Q : res -> gh -> Prop) :
  can_step t Γ -> CallPre t c arg Γ -> (forall r Γ1, Keep t Γ Γ1 -> Q r Γ1) ->
  wp t (invoke c arg) Γ Q.
Proof.
  intros Hc Hpre HQ. unfold invoke, wp. cbn. split; [exact Hc | split; [exact Hpre |]].
  intros r Γ1 H. apply HQ, H.
Qed.
