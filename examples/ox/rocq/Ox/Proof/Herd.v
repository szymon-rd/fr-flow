(** `ox.internal.ThreadHerd`, the threads of a scope: what its code does, as steps of the system of scopes.

    Each lemma is about the meaning of Ox's trees (`run more`, in any program that uses Ox) and is proven by
    walking it, an operation at a time. *)

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From Ox.Proof Require Export Setting Ghost.
Open Scope string_scope.

Definition c_herd : string := "ox.internal.ThreadHerd".
Definition c_flag : string := p_class atomic_boolean.
Definition c_set : string := p_class concurrent_set.
Definition herd_at (r : nat) : val := VObj (Ref c_herd r).
Definition m_assertNotShuttingDown : sym := Member c_herd "assertNotShuttingDown" ":scala.Unit".
Definition m_close : sym := Member c_herd "interruptAllAndJoinUntilCompleted" ":scala.Unit".
Definition m_isOwnerOrHerdThread : sym :=
  Member c_herd "isOwnerOrHerdThread" "java.lang.Thread:scala.Boolean".
Definition herdN : namespace := nroot .@ "herd".

(** A herd's fields before its initialiser has run, and after. *)
Definition herd_unset : list (string * val) :=
  [("threadFactory", vnull); ("herdOwner", vnull); ("shutdownInProgress", vnull); ("threads", vnull)].
Definition herd_fields (tf : val) (owner flag set : nat) : list (string * val) :=
  [("threadFactory", tf); ("herdOwner", VTid owner); ("shutdownInProgress", vext c_flag flag);
   ("threads", vext c_set set)].

(** `interruptIfNeeded(u)`, the closing loop's local function, walked: a thread not yet among those interrupted
    is interrupted and put among them. `"Hv1"` holds the variable of the threads interrupted, `xs`. *)
Ltac herd_interrupt xs u Hxs :=
  wp_call; wp_get "Hv1"; wp_whd; fold any; rewrite (any_thread _ xs u Hxs); [| done];
  let Hhas := fresh "Hhas" in
  destruct (has_thread xs u) eqn:Hhas;
  [ wp_done
  | wp_op; iApply wp_thread_interrupt; iNext; wp_get "Hv1"; wp_whd; fold any;
    rewrite (any_thread _ xs u Hxs); [| done]; rewrite Hhas; wp_set "Hv1"; wp_done ].

(** What the closing loop keeps is given back: the place, the two variables, what the caller is owed. *)
Ltac herd_kept :=
  iFrame "Hplace HΦ"; iSplitL "Hv1";
  [ iExists _; iFrame "Hv1"; iPureIntro; first [eassumption | by apply threads_only_app]
  | iExists _; iFrame "Hv2"; iPureIntro; first [eassumption | by left | by right] ].

Section herds.
  Context `{!jvmGS code obj Σ, !scopesGS Σ}.

  (** The herd at `r` of the scope `q`, made by `owner`: its fields no longer change; its flag is anyone's to
      read and set. *)
  Definition is_herd (r q owner : nat) : iProp Σ :=
    ∃ tf flag, r ↦obj□ (c_herd, herd_fields tf owner flag q) ∗ scope_at q ∗
      inv herdN (∃ v : bool, flag ↦ext (Held atomic_boolean v)).

  Global Instance is_herd_persistent r q owner : Persistent (is_herd r q owner).
  Proof. apply _. Qed.
End herds.

Section herd.
  Context `{!jvmGS code obj Σ, !scopesGS Σ} (more : table).
  Local Instance herd_irisGS : irisGS (jvm (run more)) Σ := jvm_irisGS (run more).

  (** ** A herd made is a scope opened, by the thread that makes it *)

  Lemma herd_init t r tf rl stack Φ :
    rl ≠ Past →
    scopes_inv -∗ place_is t (rl, stack) -∗ r ↦obj (c_herd, herd_unset) -∗
    (∀ q, is_herd r q t -∗ place_is t (rl, q :: stack) -∗ Φ (inr VUnit)) -∗
    wpP (run more) t (run more (Init c_herd) (VList [herd_at r; tf])) ⊤ Φ.
  Proof.
    iIntros (Hrl) "#Hinv Hplace Hr HΦ".
    wp_set "Hr".
    wp_op. iApply wp_current_thread. iNext. wp_set "Hr".
    wp_op. iApply wp_ext_new; [done |]. iIntros "!>" (flag) "Hflag". wp_set "Hr".
    wp_op. iApply wp_ext_new; [done |]. iIntros "!>" (q) "Hq". wp_set "Hr".
    iApply wpP_fupd.
    iMod (scopes_open with "Hinv Hplace Hq") as "[Hplace #Hscope]"; [done | done |].
    iMod (obj_at_persist with "Hr") as "#Hr".
    iMod (inv_alloc herdN ⊤ (∃ v : bool, flag ↦ext (Held atomic_boolean v)) with "[Hflag]") as "#Hflag";
      [by iExists false |].
    iModIntro. wp_done. iApply ("HΦ" with "[] Hplace"). iExists tf, flag. by iFrame "Hr Hscope Hflag".
  Qed.

  (** ** `assertNotShuttingDown` returns, or throws: it reads the herd's flag *)

  Lemma herd_assertNotShuttingDown t r q owner Φ :
    is_herd r q owner -∗ (Φ (inr VUnit) ∧ ∀ x, Φ (inl x)) -∗
    wpP (run more) t (run more (Method m_assertNotShuttingDown) (VList [herd_at r])) ⊤ Φ.
  Proof.
    iIntros "#Hherd HΦ". iDestruct "Hherd" as (tf flag) "(Hr & Hq & Hflag)".
    wp_read "Hr".
    wp_op. iApply wp_ext_call. iInv "Hflag" as (v) ">Hf" "Hclose". iModIntro. iExists atomic_boolean, v.
    iFrame "Hf". iIntros "!>" (intr choice). simpl. iIntros "Hf".
    iMod ("Hclose" with "[Hf]") as "_"; [by iExists v |]. iModIntro.
    destruct v; wp_done; [iDestruct "HΦ" as "[_ HΦ]" | iDestruct "HΦ" as "[HΦ _]"]; iApply "HΦ".
  Qed.

  (** ** `isOwnerOrHerdThread` answers: it reads the herd's owner and its set *)

  Lemma herd_isOwnerOrHerdThread t r q owner u Φ :
    scopes_inv -∗ is_herd r q owner -∗ (∀ b, Φ (inr (VBool b))) -∗
    wpP (run more) t (run more (Method m_isOwnerOrHerdThread) (VList [herd_at r; VTid u])) ⊤ Φ.
  Proof.
    iIntros "#Hinv #Hherd HΦ". iDestruct "Hherd" as (tf flag) "(Hr & Hq & Hflag)".
    wp_read "Hr". wp_whd. destruct (same_place u owner).
    - wp_done. iApply "HΦ".
    - wp_call. wp_read "Hr". wp_op. iApply (wp_set_read with "Hinv Hq"); [done |].
      iIntros "!>" (held intr choice _). iExists _. iSplit; [iPureIntro; apply set_contains |].
      wp_done. wp_done. iApply "HΦ".
  Qed.

  (** ** `interruptAllAndJoinUntilCompleted` ends and leaves the scope

      Run by the herd's owner with the scope innermost among those it has open. It returns, or throws the
      interruption it met while it joined; either way the scope has been ended and left: the loop goes on
      until the owner finds the herd's set empty, and that finding is the step. *)

  (** The loop's two variables: the threads interrupted so far, and the owner's first interruption. *)
  Definition close_vars (v1 v2 : nat) : iProp Σ :=
    (∃ xs, ⌜threads_only xs⌝ ∗ v1 ↦obj (var_class, [(var_field, vdata Library.c_set [VList xs])])) ∗
    (∃ x, ⌜x = vnull ∨ x = VExn InterruptedException⌝ ∗ v2 ↦obj (var_class, [(var_field, x)])).

  (** What each of its loops keeps: the owner's place with the scope still open, the variables, and what the
      caller is owed when the scope has been left. *)
  Definition close_keeps (t q : nat) (rl : role) (stack : list nat) (Φ : res code obj → iProp Σ)
      (v1 v2 : nat) : iProp Σ :=
    place_is t (rl, q :: stack) ∗ close_vars v1 v2 ∗
    (place_is t (rl, stack) -∗ took (Step_Leave (zt t) (zs q)) -∗
       Φ (inr VUnit) ∧ Φ (inl InterruptedException)).

  Lemma herd_close t r q rl stack Φ :
    scopes_inv -∗ is_herd r q t -∗ place_is t (rl, q :: stack) -∗
    (place_is t (rl, stack) -∗ took (Step_Leave (zt t) (zs q)) -∗
       Φ (inr VUnit) ∧ Φ (inl InterruptedException)) -∗
    wpP (run more) t (run more (Method m_close) (VList [herd_at r])) ⊤ Φ.
  Proof.
    iIntros "#Hinv #Hherd Hplace HΦ". iDestruct "Hherd" as (tf flag) "(Hr & Hq & Hflag)".
    (* assertOnOwnerThread: the caller is the owner *)
    wp_call. wp_op. iApply wp_current_thread. iNext. wp_read "Hr". wp_whd. rewrite same_place_refl. wp_done.
    (* shutdownInProgress.set(true) *)
    wp_read "Hr". wp_op. iApply wp_ext_call. iInv "Hflag" as (v) ">Hf" "Hclose". iModIntro.
    iExists atomic_boolean, v. iFrame "Hf". iIntros "!>" (intr choice). simpl. iIntros "Hf".
    iMod ("Hclose" with "[Hf]") as "_"; [by iExists true |]. iModIntro.
    (* the two variables *)
    wp_op. iApply wp_obj_new. iIntros "!>" (v1) "Hv1". iEval (simpl) in "Hv1".
    wp_op. iApply wp_obj_new. iIntros "!>" (v2) "Hv2".
    iAssert (close_vars v1 v2) with "[Hv1 Hv2]" as "Hvars".
    { iSplitL "Hv1"; [iExists []; iFrame "Hv1"; iPureIntro; constructor | iExists vnull; iFrame "Hv2"; by iLeft]. }
    (* while !threads.isEmpty *)
    wp_whd. iApply (wpP_loop_then _ _ _ _ _ _ (λ _, close_keeps t q rl stack Φ v1 v2) with "[$Hplace $Hvars $HΦ]").
    iIntros "!>" (s) "(Hplace & Hvars & HΦ)".
    wp_read "Hr". wp_op. iApply (wp_set_isEmpty with "Hinv Hq Hplace"); [done |]. iNext. iSplit.
    - (* empty: the scope is ended and left *)
      iIntros "Hplace #Hleft". wp_done.
      iDestruct "Hvars" as "[_ Hv2]". iDestruct "Hv2" as (x) "[%Hx Hv2]".
      destruct Hx as [-> | ->]; wp_get "Hv2".
      + wp_done. iDestruct ("HΦ" with "Hplace Hleft") as "[H _]". iApply "H".
      + wp_get "Hv2". wp_done. iDestruct ("HΦ" with "Hplace Hleft") as "[_ H]". iApply "H".
    - (* not empty: each thread of the set is interrupted once, then each is joined *)
      iIntros "Hplace". wp_read "Hr".
      wp_whd. iApply (wpP_loop_then _ _ _ _ _ _ (λ _, close_keeps t q rl stack Φ v1 v2) with "[$Hplace $Hvars $HΦ]").
      iIntros "!>" (passed) "(Hplace & [Hv1 Hv2] & HΦ)". iDestruct "Hv1" as (xs) "[%Hxs Hv1]".
      wp_op. iApply (wp_set_read with "Hinv Hq"); [done |]. iIntros "!>" (held intr1 choice1 Hall).
      destruct (set_next t intr1 held passed choice1) as (y & Hcall & Hy). iExists (inr y). iSplit; [done |].
      destruct Hy as [-> | (x0 & -> & Hin & _)].
      + (* the first traversal is over: the second *)
        wp_done. wp_read "Hr".
        wp_whd. iApply (wpP_loop_then _ _ _ _ _ _ (λ _, close_keeps t q rl stack Φ v1 v2) with "[$Hplace Hv1 $Hv2 $HΦ]");
          [iExists xs; by iFrame |].
        clear xs Hxs held intr1 choice1 Hall Hcall passed.
        iIntros "!>" (passed) "(Hplace & [Hv1 Hv2] & HΦ)". iDestruct "Hv1" as (xs) "[%Hxs Hv1]".
        wp_op. iApply (wp_set_read with "Hinv Hq"); [done |]. iIntros "!>" (held intr1 choice1 Hall).
        destruct (set_next t intr1 held passed choice1) as (y & Hcall & Hy). iExists (inr y). iSplit; [done |].
        destruct Hy as [-> | (x0 & -> & Hin & _)].
        * wp_done. wp_done. iFrame "Hplace Hv2 HΦ". iExists xs. by iFrame.
        * destruct (Hall x0 Hin) as [u ->]. iDestruct "Hv2" as (x) "[%Hx Hv2]". wp_call. herd_interrupt xs u Hxs.
          all: wp_op; iApply wp_thread_join_any; iNext; iSplit.
          1,3: wp_done; wp_done; herd_kept.
          (* interrupted while it joined: the first interruption is kept, to be thrown at the end *)
          all: destruct Hx as [-> | ->]; wp_get "Hv2".
          1,3: wp_set "Hv2"; wp_done; wp_done; herd_kept.
          all: wp_get "Hv2"; wp_done; wp_done; herd_kept.
      + destruct (Hall x0 Hin) as [u ->]. wp_call. herd_interrupt xs u Hxs.
        all: wp_done; wp_done; iFrame "Hplace Hv2 HΦ"; iExists _; iFrame "Hv1"; iPureIntro.
        all: first [eassumption | by apply threads_only_app].
  Qed.

End herd.
