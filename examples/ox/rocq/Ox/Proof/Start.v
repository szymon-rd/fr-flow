(** `ThreadHerd.startThread`: a fork made, and the thread it starts.

    `verifyCurrentThreadInScopeTree` first: it reads the calling thread's scope and walks the capabilities
    that enclose it, asking each one's herd whether the thread is its owner or one of its threads. It returns
    or throws; nothing of the scopes is changed by it. *)

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From Ox.Proof Require Export Context.
Open Scope string_scope.

Definition m_verify : sym := Member c_herd "verifyCurrentThreadInScopeTree" ":scala.Unit".
Definition m_startThread : sym := Member c_herd "startThread" "scala.Function0:scala.Unit".

Section start.
  Context `{!jvmGS code obj Σ, !scopesGS Σ} (more : table).
  Local Instance start_irisGS : irisGS (jvm (run more)) Σ := jvm_irisGS (run more).

  Lemma herd_verify t r q owner pl Φ :
    ctx_inv -∗ scopes_inv -∗ is_herd r q owner -∗ place_is t pl -∗
    (place_is t pl -∗ (Φ (inr VUnit) ∧ ∀ x, Φ (inl x))) -∗
    wpP (run more) t (run more (Method m_verify) (VList [herd_at r])) ⊤ Φ.
  Proof.
    iIntros "#Hctx #Hinv #Hherd Hplace HΦ".
    wp_op. iApply wp_current_thread. iNext.
    (* currentScope.get() *)
    wp_whd. wp_leaf. iApply (ctx_named with "Hctx Hplace"). iIntros (cfields) "#Hc #Hready Hplace".
    iDestruct "Hready" as (tl) "[[%Hcs %Hcw] Hlocal]".
    wp_op. iApply wp_obj_get. iModIntro. iExists _, _, _, _. iFrame "Hc". iSplit; [done |].
    iIntros "!> _ !>". wp_done.
    wp_op. iApply wp_ext_call. iInv "Hlocal" as (s) "[>Htl #Hs]" "Hclose". iModIntro.
    iExists thread_local, s. iFrame "Htl". iIntros "!>" (intr choice). cbn. iIntros "Htl".
    iDestruct (local_of s t with "Hs") as "#Hv".
    iMod ("Hclose" with "[Htl]") as "_"; [iNext; iExists s; by iFrame "Htl Hs" |]. iModIntro.
    iClear "Hs". iRevert "Hv". generalize (of_thread s t). intros v. iIntros "#Hv". clear s intr choice.
    iDestruct ("HΦ" with "Hplace") as "HΦ".
    iDestruct "Hv" as "[-> | [%n Hcap]]".
    - (* the thread is in no scope: it throws *)
      wp_done. wp_op. iApply wp_current_thread. iNext. wp_done. wp_done.
      iDestruct "HΦ" as "[_ H]". iApply "H".
    - (* in a scope: `doAssert` walks the capabilities that enclose it *)
      destruct n as [| n]; [done |]. iPoseProof "Hcap" as "Hcap'".
      iDestruct "Hcap'" as (r1 fields1 h1 q1 o1 p1) "(-> & _)".
      wp_done. wp_whd.
      lazymatch goal with
      | |- environments.envs_entails _ (wpP _ _ (Call ?c _ _) _ _) => set (doAssert := c)
      end.
      iAssert (□ ∀ k v Ψ, is_cap k v -∗ (Ψ (inr VUnit) ∧ ∀ x, Ψ (inl x)) -∗
                 wpP (run more) t (run more doAssert (VList [v])) ⊤ Ψ)%I as "#Hassert".
      { iIntros "!>" (k). iInduction k as [| k] "IH"; iIntros (v Ψ) "#Hk HΨ"; [done |].
        iDestruct "Hk" as (r0 fields h0 q0 o0 p0) "(-> & Hr0 & [%Hfh [%Hwh [%Hfp %Hwp]]] & Hh0 & Hp0)".
        wp_call. wp_op. iApply wp_obj_get. iModIntro. iExists _, _, _, _. iFrame "Hr0". iSplit; [done |].
        iIntros "!> _ !>". wp_done.
        wp_call. iApply (herd_isOwnerOrHerdThread with "Hinv Hh0"). iIntros ([]).
        - wp_done. iDestruct "HΨ" as "[H _]". iApply "H".
        - (* not this herd's: the capability it was made in, if there is one *)
          wp_call. wp_op. iApply wp_obj_get. iModIntro. iExists _, _, _, _. iFrame "Hr0".
          iSplit; [done |]. iIntros "!> _ !>".
          iDestruct "Hp0" as "[-> | [%p' [-> Hp']]]".
          + (* none: it throws *)
            wp_done. wp_done. iDestruct "HΨ" as "[_ H]". iApply "H".
          + (* one: the same of it *)
            destruct k as [| k]; [done |]. iPoseProof "Hp'" as "Hp''".
            iDestruct "Hp''" as (r2 fields2 h2 q2 o2 p2) "(-> & _)".
            wp_done. wp_whd. iApply wpP_call_then. iNext. iApply ("IH" with "Hp'"). iSplit.
            * wp_done. iDestruct "HΨ" as "[H _]". iApply "H".
            * iIntros (x). wp_done. iDestruct "HΨ" as "[_ H]". iApply "H". }
      iApply wpP_call_then. iNext. iApply ("Hassert" with "Hcap"). iSplit.
      + wp_done. wp_done. iDestruct "HΦ" as "[H _]". iApply "H".
      + iIntros (x). wp_done. wp_done. iDestruct "HΦ" as "[_ H]". iApply "H".
  Qed.

End start.
