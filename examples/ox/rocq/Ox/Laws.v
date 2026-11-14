(** The laws of a scope, as far as they are proven of Ox's code.

    Seventeen laws say what a library of scopes and forks owes its users (`docs/THREADS.md`; the literature has no
    such list: `reports/`). This file states those that are theorems here, over the configurations Ox's code
    reaches by any order of its threads' steps, for every client that keeps `client_ok`, from the contracts of
    `FrFlow.Threads.Jdk` (`Ox/Tree/Assumed.v` says which the code uses) and the memory model (`Ox/Tree/Memory.v`).

    A scope is a thread herd: `h` names it by its set of threads. "Completed" is `h_exited`: its closing loop
    has found its set empty. That is where a scope returns or throws: `ApiProofs.scopedWithCapability_spec` says
    that whatever the body and the closing do, what follows `scopedWithCapability` finds the herd no longer among
    its owner's open herds (`popped`), and a herd its owner has not open is completed (`i_open`).

    | Law | Here |
    |---|---|
    | 1. Containment: a completed scope has no fork with an operation left | `scope_contained`, `program_contained` |
    | 2. Tree: a scope opened inside a completed scope is completed | `scopes_nest` |
    | 3. No start after close: a completed scope's set stays empty | `scope_contained` (its first part) |
    | 3. A refused fork leaves no trace | false of Ox: `forkUser` counts before it is refused (`examples/ox/probe`) |
    | 4. Confinement | the premise `client_ok`; not enforced by Ox |
    | 5 to 17 | not proven: the supervisor, the futures, finalizers, fork locals, `par`, `race` and progress |

    All of it rests on `TsIsEmpty`, which the JDK does not keep (`Jdk.v`; `examples/ox/probe/IsEmptyProbe.scala`):
    these are theorems about Ox over a set whose emptiness test is exact. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps Ox.Inner Ox.HerdProofs
  Ox.ScopeProofs Ox.Main.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

(** ** What no step undoes

    Of the ghost state, along a run: a herd keeps its owner and the herd it was opened inside, a herd completed
    stays completed, and a thread that is a fork of a herd stays one. *)

Record Stays (Γ Γ' : gh) : Prop := {
  s_herd : forall h hr, g_herd Γ h = Some hr -> exists hr', g_herd Γ' h = Some hr' /\
      h_owner hr' = h_owner hr /\ h_parent hr' = h_parent hr /\ (h_exited hr = true -> h_exited hr' = true);
  s_fork : forall u h b, g_role Γ u = ForkOf h b -> g_role Γ' u = ForkOf h b }.

Arguments s_herd {Γ Γ'} _ {h hr} _.
Arguments s_fork {Γ Γ'} _ {u h b} _.

Lemma stays_refl Γ : Stays Γ Γ.
Proof. constructor; intros; eauto 10. Qed.

Lemma stays_trans Γ1 Γ2 Γ3 : Stays Γ1 Γ2 -> Stays Γ2 Γ3 -> Stays Γ1 Γ3.
Proof.
  intros [A1 A2] [B1 B2]. constructor; intros.
  - destruct (A1 _ _ H) as (hr' & E' & O' & P' & X').
    destruct (B1 _ _ E') as (hr'' & E'' & O'' & P'' & X'').
    exists hr''. repeat split; try congruence; auto.
  - auto.
Qed.

(** A step of one thread keeps it: it is what every other thread relies on. *)
Lemma guar_stays t Γ Γ' : Logic.Guar Rely t Γ Γ' -> Stays Γ Γ'.
Proof.
  intro HG. assert (HR : Rely (S t) Γ Γ') by (apply HG; lia). constructor.
  - intros h hr H. destruct (r_herd HR H) as (hr' & E & O & P & _ & X & _). exists hr'. auto.
  - intros u h b H. exact (r_fork HR H).
Qed.

Lemma moves_stays Γ Γ' : Logic.moves Rely Γ Γ' -> Stays Γ Γ'.
Proof.
  induction 1 as [Γ | Γ Γ' Γ'' _ IH Hm]; [apply stays_refl |].
  eapply stays_trans; [exact IH |]. destruct Hm as [-> | (t & HG)]; [apply stays_refl | exact (guar_stays HG)].
Qed.

(** ** Law 2: scopes nest

    A scope opened inside a completed scope is completed: by the completed scope's owner (its open scopes are a
    stack, each opened inside the next), or by one of its forks (which has taken itself out, and so owns no
    open scope). So an inner scope completes before the one enclosing it. *)

Theorem scopes_nest σ Γ h hr h' hr' :
  Inv σ Γ -> g_herd Γ h = Some hr -> h_exited hr = true ->
  g_herd Γ h' = Some hr' -> h_parent hr' = Some h -> h_exited hr' = true.
Proof.
  intros HI Hh Hx Hh' Hp. destruct (h_exited hr') eqn:E; trivial. exfalso.
  assert (Hin : In h' (g_open Γ (h_owner hr'))) by (apply (i_open HI); exists hr'; auto).
  apply in_split in Hin. destruct Hin as (pre & post & Hsplit).
  pose proof (i_stack HI Hsplit Hh') as Hst. rewrite Hp in Hst.
  destruct post as [| h1 post].
  - (* opened by a fork of `h`, which has taken itself out *)
    destruct (g_role Γ (h_owner hr')) as [| | t th b | h0 b] eqn:Hr; cbn in Hst; try discriminate.
    injection Hst as <-. pose proof (i_exit HI Hh Hx Hr) as Hrm.
    destruct (i_removed HI Hrm) as (Hopen & _). rewrite Hopen in Hsplit. destruct pre; discriminate.
  - (* opened by the owner of `h`, inside `h`: then `h` is still open *)
    injection Hst as <-.
    assert (Hin1 : In h (g_open Γ (h_owner hr'))).
    { rewrite Hsplit. apply in_or_app. right. right. left. reflexivity. }
    apply (i_open HI) in Hin1. destruct Hin1 as (hr1 & E1 & _ & X1).
    rewrite Hh in E1. injection E1 as <-. rewrite Hx in X1. discriminate.
Qed.

Section Laws.

  Variable client : nat -> list OxError -> val -> M val.
  Hypothesis client_ok : forall t n caps arg Γ, CallPre t (Client n caps) arg Γ ->
    wp t (client n caps arg) Γ (fun _ Γ' => Keep t Γ Γ').

  (** A configuration, with the ghost state the proof gives it. *)
  Definition reached_with (c : config code obj) (Γ : gh) : Prop :=
    Logic.good_with Inv Rely Active CallPre CallPost StartPre Done c Γ.

  (** Every configuration the threads reach has one. *)
  Lemma reached_has n0 c : steps (interp client) (init client n0) c -> exists Γ, reached_with c Γ.
  Proof. intro Hs. exact (reached_good client client_ok n0 c Hs). Qed.

  (** And from one configuration to a later one, the ghost state moves only as `Stays` allows. *)
  Lemma later_has c c' Γ :
    reached_with c Γ -> steps (interp client) c c' -> exists Γ', reached_with c' Γ' /\ Stays Γ Γ'.
  Proof.
    intros Hg Hs.
    destruct (Logic.sound_with Rely_refl Rely_trans (call_ok client client_ok) (start_ok client) exit_ok Hg Hs)
      as (Γ' & Hg' & Hm).
    exists Γ'. split; [exact Hg' | exact (moves_stays Hm)].
  Qed.

  (** ** Laws 1 and 3: a completed scope is contained, and stays closed

      Once a scope has completed, in every configuration reached after: it is completed; its set of threads
      is empty, so no thread is ever added to it again; and no fork of it has an operation left. Of any scope,
      at any depth, while the rest of the program runs on. *)

  Theorem scope_contained c Γ h hr c' :
    reached_with c Γ -> g_herd Γ h = Some hr -> h_exited hr = true -> steps (interp client) c c' ->
    exists Γ' hr', reached_with c' Γ' /\ Stays Γ Γ' /\ g_herd Γ' h = Some hr' /\ h_exited hr' = true /\
      (exists s, j_ts (c_st c') h = Some s /\ forall u, s u = false) /\
      forall u b p, g_role Γ' u = ForkOf h b -> c_pool c' u = Some p -> exists r, p = Ret r.
  Proof.
    intros Hg Hh Hx Hs. destruct (later_has Hg Hs) as (Γ' & Hg' & HS).
    destruct (s_herd HS Hh) as (hr' & Hh' & _ & _ & Hx'). specialize (Hx' Hx).
    exists Γ', hr'. destruct Hg' as (HI' & Hpool').
    split; [split; assumption |]. split; [exact HS |]. split; [exact Hh' |]. split; [exact Hx' |]. split.
    - eapply exited_empty; eassumption.
    - intros u b p Hr Hp. destruct (Hpool' u p Hp) as (Hst & Γu & HR & Hw).
      destruct p as [a | X o k | S B body s k | c0 arg k]; [eauto | | |]; exfalso.
      all: assert (Hact : Active u Γ') by (eapply wp_active; eauto; intros a E; discriminate).
      all: unfold Active in Hact; rewrite (i_exit HI' Hh' Hx' Hr) in Hact; discriminate.
  Qed.

  (** Law 1 of the whole program: once the first thread has ended, no thread has an operation left. *)
  Theorem program_contained n0 c :
    steps (interp client) (init client n0) c ->
    (exists code0 i, j_th (c_st c) main = Some (Thread code0 TTerminated i)) ->
    forall u p, c_pool c u = Some p -> exists r, p = Ret r.
  Proof. exact (contained client client_ok n0 c). Qed.

End Laws.
