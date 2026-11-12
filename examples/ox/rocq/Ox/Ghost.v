(** What the proof of containment records beside the JDK's state, and the invariant.

    For each thread herd (named by its set of threads): its owner, whether its closing loop has found it empty
    (`h_exited`), the herd it was opened inside (`h_parent`), and when it was opened (`h_stamp`). For each thread:
    what it is (`g_role`: the first thread, a thread made and not yet in a set, a fork of a herd), whether it has
    taken itself out of its herd's set (`g_removed`), and the herds it owns that are still open, innermost first
    (`g_open`). *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Code.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Abbreviation jst := (Jdk.jst code obj).

Definition main : tid := 0.

Record hrec := mkH { h_owner : tid; h_exited : bool; h_parent : option nat; h_stamp : nat }.

Inductive role :=
  | NoRole
  | Main
  | Created (t : tid) (th : ThreadHerd) (b : code)     (* made by `t` for a herd, not yet in its set *)
  | ForkOf (h : nat) (b : code).                       (* in herd `h`'s set, or once in it *)

Record gh := mkG {
  g_herd : nat -> option hrec;
  g_role : tid -> role;
  g_removed : tid -> bool;
  g_open : tid -> list nat;
  g_fin : nat -> bool;                (* an AtomicReference that holds a scope's finalizers *)
  g_clock : nat }.

Definition member_herd (r : role) : option nat :=
  match r with ForkOf h _ => Some h | _ => None end.

(** A thread that has started, whether or not it has ended. *)
Definition begun (σ : jst) (u : tid) : Prop :=
  match j_th σ u with Some (Thread _ TStarted _) | Some (Thread _ TTerminated _) => True | _ => False end.

Record Inv (σ : jst) (Γ : gh) : Prop := {
  (* a herd's set holds its forks that have not taken themselves out *)
  i_herd : forall h hr, g_herd Γ h = Some hr -> exists s, j_ts σ h = Some s /\
      forall u, s u = true <-> ((exists b, g_role Γ u = ForkOf h b) /\ g_removed Γ u = false);
  (* a herd found empty by its closing loop has no fork left *)
  i_exit : forall h hr, g_herd Γ h = Some hr -> h_exited hr = true ->
      forall u b, g_role Γ u = ForkOf h b -> g_removed Γ u = true;
  (* a thread's open herds are those it owns that are not exited *)
  i_open : forall u h, In h (g_open Γ u) <->
      exists hr, g_herd Γ h = Some hr /\ h_owner hr = u /\ h_exited hr = false;
  i_nodup : forall u, NoDup (g_open Γ u);
  (* a herd was opened inside the next of its owner's open herds, or inside the herd its owner is a fork of *)
  i_stack : forall u pre h post hr, g_open Γ u = pre ++ h :: post -> g_herd Γ h = Some hr ->
      h_parent hr = match post with h1 :: _ => Some h1 | [] => member_herd (g_role Γ u) end;
  i_stamp : forall h hr h1, g_herd Γ h = Some hr -> h_parent hr = Some h1 ->
      exists hr1, g_herd Γ h1 = Some hr1 /\ h_stamp hr1 < h_stamp hr;
  i_clock : forall h hr, g_herd Γ h = Some hr -> h_stamp hr < g_clock Γ;
  (* a thread that has taken itself out of its herd is a fork and owns no open herd *)
  i_removed : forall u, g_removed Γ u = true -> g_open Γ u = [] /\ exists h b, g_role Γ u = ForkOf h b;
  (* a thread that has not started has done nothing *)
  i_new : forall u, ~ begun σ u -> g_removed Γ u = false /\ g_open Γ u = [];
  i_none : forall u, j_th σ u = None -> g_role Γ u = NoRole;
  i_created : forall u t th b, g_role Γ u = Created t th b ->
      exists i, j_th σ u = Some (Thread (Lam_ThreadHerd_startThread_1 th b) TNew i);
  i_fork : forall u h b, g_role Γ u = ForkOf h b -> g_herd Γ h <> None /\
      exists th st i, j_th σ u = Some (Thread (Lam_ThreadHerd_startThread_1 th b) st i) /\
        ThreadHerd_threads th = h;
  i_started : forall u, begun σ u -> g_role Γ u = Main \/ exists h b, g_role Γ u = ForkOf h b;
  i_main : forall u, g_role Γ u = Main -> u = main;
  (* a scope's finalizers: none registered, or taken *)
  i_fin : forall r, g_fin Γ r = true -> j_ar σ r = Some None \/ j_ar σ r = Some (Some (VList []));
  (* the first thread ends owning no open herd *)
  i_done : (exists c i, j_th σ main = Some (Thread c TTerminated i)) -> g_open Γ main = [] }.

Arguments i_herd {σ Γ} _ {h hr} _.
Arguments i_exit {σ Γ} _ {h hr} _ _ {u b} _.
Arguments i_open {σ Γ} _ u h.
Arguments i_nodup {σ Γ} _ u.
Arguments i_stack {σ Γ} _ {u pre h post hr} _ _.
Arguments i_stamp {σ Γ} _ {h hr h1} _ _.
Arguments i_clock {σ Γ} _ {h hr} _.
Arguments i_removed {σ Γ} _ {u} _.
Arguments i_new {σ Γ} _ {u} _.
Arguments i_none {σ Γ} _ {u} _.
Arguments i_created {σ Γ} _ {u t th b} _.
Arguments i_fork {σ Γ} _ {u h b} _.
Arguments i_started {σ Γ} _ {u} _.
Arguments i_main {σ Γ} _ {u} _.
Arguments i_fin {σ Γ} _ {r} _.
Arguments i_done {σ Γ} _ _.

(** What the steps of other threads may do to the ghost state, as thread `t` sees it: a herd keeps its owner,
    its parent and its stamp, and stays exited once it is; `t`'s own herds are exited by `t` alone; roles once
    given stay; `t`'s own flags are `t`'s. *)
Record Rely (t : tid) (Γ Γ' : gh) : Prop := {
  r_herd : forall h hr, g_herd Γ h = Some hr -> exists hr', g_herd Γ' h = Some hr' /\
      h_owner hr' = h_owner hr /\ h_parent hr' = h_parent hr /\ h_stamp hr' = h_stamp hr /\
      (h_exited hr = true -> h_exited hr' = true) /\
      (h_owner hr = t -> h_exited hr' = h_exited hr);
  r_fork : forall u h b, g_role Γ u = ForkOf h b -> g_role Γ' u = ForkOf h b;
  r_main : forall u, g_role Γ u = Main -> g_role Γ' u = Main;
  r_created : forall u th b, g_role Γ u = Created t th b -> g_role Γ' u = Created t th b;
  r_removed : g_removed Γ' t = g_removed Γ t;
  r_open : g_open Γ' t = g_open Γ t;
  r_fin : forall r, g_fin Γ r = true -> g_fin Γ' r = true }.

Arguments r_herd {t Γ Γ'} _ {h hr} _.
Arguments r_fork {t Γ Γ'} _ {u h b} _.
Arguments r_main {t Γ Γ'} _ {u} _.
Arguments r_created {t Γ Γ'} _ {u th b} _.
Arguments r_removed {t Γ Γ'} _.
Arguments r_open {t Γ Γ'} _.
Arguments r_fin {t Γ Γ'} _ {r} _.

Lemma Rely_refl t Γ : Rely t Γ Γ.
Proof. constructor; intros; eauto 10. Qed.

Lemma Rely_trans t Γ1 Γ2 Γ3 : Rely t Γ1 Γ2 -> Rely t Γ2 Γ3 -> Rely t Γ1 Γ3.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7] [B1 B2 B3 B4 B5 B6 B7]. constructor; intros.
  - destruct (A1 _ _ H) as (hr' & E' & O' & P' & S' & X' & M').
    destruct (B1 _ _ E') as (hr'' & E'' & O'' & P'' & S'' & X'' & M'').
    exists hr''. repeat split; try congruence; auto.
    intro Ho. rewrite M'' by congruence. auto.
  - auto.
  - auto.
  - auto.
  - congruence.
  - congruence.
  - auto.
Qed.

Definition Guar (t : tid) (Γ Γ' : gh) : Prop := Logic.Guar Rely t Γ Γ'.

(** A thread may still take steps until it has taken itself out of its herd. *)
Definition Active (t : tid) (Γ : gh) : Prop := g_removed Γ t = false.
