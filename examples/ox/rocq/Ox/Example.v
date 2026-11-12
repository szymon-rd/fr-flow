(** A client, and containment for it with nothing left to assume of it.

    In Scala:

      supervised {                                   // closure 1, given the scope's capability
        forkUser {                                   // closure 2, holding that capability
          fork { work() }                            // closure 3
          unsupervised {                             // closure 4, holding the outer capability, given the inner
            forkUnsupervised { work() }              // closure 3 again, forked in the inner scope, holding the outer
          }
        }
        work()
      }

    `work()` is the client's own: it touches nothing of Ox's. *)

From Stdlib Require Import ZArith List Bool String Lia.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Logic
  FrFlow.Threads.Lang.
Require Import Ox.Gen Ox.Ghost Ox.Facts Ox.Specs Ox.Frame Ox.Updates Ox.Steps Ox.Inner Ox.HerdProofs
  Ox.ScopeProofs Ox.Main Ox.ApiProofs.
Import ListNotations.
Open Scope list_scope.
Open Scope prog_scope.
Open Scope string_scope.

Definition work : M val := extern "client.work".

Definition client (n : nat) (caps : list OxError) (arg : val) : M val :=
  match n, caps, arg with
  | 0, _, _ => supervised (Client 1 [])
  | 1, _, VObj (O_OxError cap) =>
      _ <- forkUser (Client 2 [cap]) cap ;;
      work
  | 2, [cap], _ =>
      _ <- fork (Client 3 []) cap ;;
      unsupervised_1 (Client 4 [cap])
  | 4, [outer], VObj (O_OxError inner) =>
      _ <- forkUnsupervised (Client 3 [outer]) inner ;;
      ret VUnit
  | _, _, _ => work
  end.

Lemma work_ok t Γ : g_removed Γ t = false -> wp t work Γ (fun _ Γ' => Keep t Γ Γ').
Proof.
  intro Hrm. apply (wp_fo t _ Γ _ (fun Γ' => Keep t Γ Γ')); [apply fo_extern | | | apply Keep_refl | auto].
  - intros Γ1 Γ2 HK HR. exact (Keep_Rely HK HR).
  - intros Γ1 HK. rewrite (k_removed HK). exact Hrm.
Qed.

(** The client keeps to what is asked of it. *)
Theorem client_ok t n caps arg Γ :
  CallPre t (Client n caps) arg Γ -> wp t (client n caps arg) Γ (fun _ Γ' => Keep t Γ Γ').
Proof.
  intros (_ & Hrm & Hk & Ha & _). cbn in Hk.
  destruct n as [| [| [| [| [| n]]]]].
  - (* the first thread: a supervised scope *)
    cbn. apply supervised_spec; [| auto]. split; [exact Hrm |]. split; [exact I | constructor].
  - (* the scope's body *)
    destruct arg as [| | | | [cap | |] | | |]; try (apply work_ok; exact Hrm). cbn.
    apply Forall_app in Hk. destruct Hk as (_ & Hkc). cbn in Hkc. apply Forall_cons_iff in Hkc.
    destruct Hkc as (Hkc & _).
    apply wp_bind. apply forkUser_spec.
    + split; [exact Hrm |]. split; [exact Hkc |]. split; [exact I |]. split; [exact I |]. split; [exact I |].
      cbn. constructor; [| constructor]. split; [exact (proj1 Hkc) | left; constructor].
    + intros [e | fk] Γ1 HK1; [exact HK1 |].
      eapply wp_mono; [| apply work_ok; rewrite (k_removed HK1); exact Hrm].
      intros r Γ2 HK2. exact (Keep_trans HK1 HK2).
  - (* a user fork *)
    destruct caps as [| cap [| c2 caps]]; try (apply work_ok; exact Hrm). cbn.
    cbn in Hk. apply Forall_cons_iff in Hk. destruct Hk as (Hkc & _).
    apply wp_bind. apply fork_spec.
    + split; [exact Hrm |]. split; [exact Hkc |]. split; [exact I |]. split; [exact I |]. split; [exact I |].
      constructor.
    + intros [e | fk] Γ1 HK1; [exact HK1 |].
      apply unsupervised_1_spec.
      * split; [rewrite (k_removed HK1); exact Hrm |]. split; [exact I |].
        cbn. constructor; [exact (knows_Keep HK1 Hkc) | constructor].
      * intros r Γ2 HK2. exact (Keep_trans HK1 HK2).
  - apply work_ok. exact Hrm.
  - (* the inner scope's body *)
    destruct caps as [| outer [| c2 caps]]; try (apply work_ok; exact Hrm).
    destruct arg as [| | | | [inner | |] | | |]; try (apply work_ok; exact Hrm). cbn [client].
    cbn in Hk. apply Forall_cons_iff in Hk. destruct Hk as (Hko & Hk).
    apply Forall_cons_iff in Hk. destruct Hk as (Hki & _).
    pose proof (Ha inner eq_refl) as Hinn.
    apply wp_bind. apply forkUnsupervised_spec.
    + split; [exact Hrm |]. split; [exact Hki |]. split; [exact I |]. split; [exact I |]. split; [exact I |].
      cbn. constructor; [| constructor]. split; [exact (proj1 Hko) |].
      right. split; [exact Hinn | exact (proj2 Hko)].
    + intros [e | fk] Γ1 HK1; [exact HK1 |]. apply wp_ret. exact HK1.
  - apply work_ok. exact Hrm.
Qed.

(** Containment for this client: when the first thread has ended, no thread has an operation left. *)
Theorem example_contained c :
  steps (interp client) (init client 0) c ->
  (exists code0 i, j_th (c_st c) main = Some (Thread code0 TTerminated i)) ->
  forall u p, c_pool c u = Some p -> exists r, p = Ret r.
Proof. apply (contained client client_ok 0). Qed.
