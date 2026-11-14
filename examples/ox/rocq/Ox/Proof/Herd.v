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
Definition herdN : namespace := nroot .@ "herd".

(** A herd's fields before its initialiser has run, and after. *)
Definition herd_unset : list (string * val) :=
  [("threadFactory", vnull); ("herdOwner", vnull); ("shutdownInProgress", vnull); ("threads", vnull)].
Definition herd_fields (tf : val) (owner flag set : nat) : list (string * val) :=
  [("threadFactory", tf); ("herdOwner", VTid owner); ("shutdownInProgress", vext c_flag flag);
   ("threads", vext c_set set)].

Section herd.
  Context `{!jvmGS code obj Σ, !scopesGS Σ} (more : table).
  Local Instance herd_irisGS : irisGS (jvm (run more)) Σ := jvm_irisGS (run more).

  (** The herd at `r` of the scope `q`, made by `owner`: its fields no longer change; its flag is anyone's to
      read and set. *)
  Definition is_herd (r q owner : nat) : iProp Σ :=
    ∃ tf flag, r ↦obj□ (c_herd, herd_fields tf owner flag q) ∗ scope_at q ∗
      inv herdN (∃ v : bool, flag ↦ext (Held atomic_boolean v)).

  Global Instance is_herd_persistent r q owner : Persistent (is_herd r q owner).
  Proof. apply _. Qed.

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

End herd.
