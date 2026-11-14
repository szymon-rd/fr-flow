(** `unsupervised(body)`: a scope with no supervisor, opened inside the scope the thread is in, if any.

    It reads the fork locals of the thread's current scope (`currentLocals`), makes the capability (`OxError`,
    with a new herd: the scope is opened here), and runs the body in it (`scopedWithCapability`). *)

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From Ox.Proof Require Export Scope.
Open Scope string_scope.

Definition m_currentLocals : sym := Member c_ctx "currentLocals" ":".
Definition m_unsupervised : sym := Member c_scopes "unsupervised" "1,scala.Function1:java.lang.Object".
Definition c_locals : string := "ox.ForkLocalMap".

Section unsupervised.
  Context `{!jvmGS code obj Σ, !scopesGS Σ} (more : table).
  Local Instance unsupervised_irisGS : irisGS (jvm (run more)) Σ := jvm_irisGS (run more).

  (** ** `currentLocals`: the fork locals of the scope the thread is in, or none *)

  Lemma current_locals t pl Φ :
    ctx_inv -∗ place_is t pl -∗
    (∀ l, ⌜plain l⌝ -∗ place_is t pl -∗ Φ (inr l)) -∗
    wpP (run more) t (run more (Method m_currentLocals) (VList [vref c_ctx ctx_at])) ⊤ Φ.
  Proof.
    iIntros "#Hctx Hplace HΦ".
    ctx_local ltl. local_get t prev "Hprev". iDestruct "Hprev" as "[-> | [%n Hcap]]".
    - (* in no scope: `ForkLocalMap(Map.empty)` *)
      wp_done. wp_op. iApply wp_obj_new. iIntros "!>" (lm) "Hlm".
      wp_call. wp_set "Hlm". wp_done. wp_done. wp_done. by iApply ("HΦ" with "[] Hplace").
    - destruct n as [| n]; [done |].
      iDestruct "Hcap" as (r fields h q o p) "(-> & Hr & [%Hfh [%Hwh [%Hfp %Hwp]]] & Hh & Hp & %Hl)".
      destruct Hl as (l & Hfl & Hwl & Hpl).
      (* in a scope: its locals *)
      wp_done. wp_call. wp_op. iApply wp_obj_get. iModIntro. iExists _, _, _, _. iFrame "Hr".
      iSplit; [done |]. iIntros "!> _ !>". repeat wp_done. by iApply ("HΦ" with "[] Hplace").
  Qed.

End unsupervised.
