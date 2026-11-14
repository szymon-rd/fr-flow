(** `ox.internal.ScopeContext`: the scope each thread is in (`currentScope`, a thread local), and the scopes
    themselves as the code holds them (`OxError`, a capability: its herd and the capability it was made in).

    The object that holds `currentScope` is initialised by the first thread that names it (`Modules.v`). What
    is known of it once initialised: `currentScope` is a thread local whose values are no object or
    capabilities. A capability's fields do not change; its herd is a herd (`Herd.v`). *)

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From FrFlow.Scala Require Export Modules.
From Ox.Proof Require Export Herd.
Open Scope string_scope.

Definition c_ctx : string := "ox.internal.ScopeContext$package$".
Definition ctx_at : nat := 10.
Definition ctx_unset : list (string * val) := [("currentScope", vnull)].
Definition c_local : string := p_class thread_local.
Definition c_cap : string := "ox.OxError".
Definition localN : namespace := nroot .@ "local".

Section context.
  Context `{!jvmGS code obj Σ, !scopesGS Σ}.

  (** A capability, at most `n` capabilities from one made in no other. *)
  Fixpoint is_cap (n : nat) (v : val) : iProp Σ :=
    match n with
    | O => False
    | S n' =>
        ∃ r fields h q o p, ⌜v = VObj (Ref c_cap r)⌝ ∗ r ↦obj□ (c_cap, fields) ∗
          ⌜field fields "herd" = Some (herd_at h) ∧ writer fields "herd" = None ∧
           field fields "parent" = Some p ∧ writer fields "parent" = None⌝ ∗
          is_herd h q o ∗ (⌜p = Library.none⌝ ∨ ∃ p', ⌜p = Library.some p'⌝ ∗ is_cap n' p')
    end%I.

  Global Instance is_cap_persistent n v : Persistent (is_cap n v).
  Proof. revert v. induction n; intros v; apply _. Qed.

  Definition scope_or_null (v : val) : iProp Σ := ⌜v = vnull⌝ ∨ ∃ n, is_cap n v.

  Lemma scope_or_null_obj (v : val) : scope_or_null v -∗ ⌜∃ o, v = VObj o⌝.
  Proof.
    iIntros "[-> | [%n H]]"; [by iExists Null |]. destruct n as [| n]; [done |].
    iDestruct "H" as (r fields h q o p) "(-> & _)". by iExists _.
  Qed.

  Lemma scope_or_null_plain (v : val) : scope_or_null v -∗ ⌜plain v⌝.
  Proof.
    iIntros "[-> | [%n H]]"; [done |]. destruct n as [| n]; [done |].
    iDestruct "H" as (r fields h q o p) "(-> & _)". done.
  Qed.

  (** The thread local: each thread's value is no object or a capability. *)
  Definition local_inv (tl : nat) : iProp Σ :=
    inv localN (∃ s : list (tid * val), tl ↦ext (Held thread_local s) ∗ [∗ list] e ∈ s, scope_or_null e.2).

  (** What is known of the object once it is initialised. *)
  Definition ctx_ready (fields : list (string * val)) : iProp Σ :=
    ∃ tl, ⌜field fields "currentScope" = Some (vext c_local tl) ∧ writer fields "currentScope" = None⌝ ∗
      local_inv tl.

  Definition ctx_inv : iProp Σ := module_inv ctx_at c_ctx ctx_unset place_tok ctx_ready.

  Local Transparent of_thread.
  Lemma local_of (s : list (tid * val)) (t : tid) :
    ([∗ list] e ∈ s, scope_or_null e.2) -∗ scope_or_null (of_thread s t).
  Proof.
    iIntros "H". iInduction s as [| [u v] rest] "IH"; [by iLeft |].
    iDestruct "H" as "[Hv Hrest]". cbn. destruct (Nat.eqb u t); [done | by iApply "IH"].
  Qed.
  Local Opaque of_thread.

  Context (more : table).
  Local Instance context_irisGS : irisGS (jvm (run more)) Σ := jvm_irisGS (run more).

  (** ** The object named: by any thread that holds its place, which it keeps *)

  Local Transparent module_init.

  Lemma ctx_named t pl Φ :
    ctx_inv -∗ place_is t pl -∗
    (∀ fields, ctx_at ↦obj□ (c_ctx, fields) -∗ ctx_ready fields -∗ place_is t pl -∗
       Φ (Ok (vref c_ctx ctx_at))) -∗
    wpP (run more) t (module_init c_ctx ctx_at) ⊤ Φ.
  Proof.
    iIntros "#Hctx Hplace HΦ". iDestruct (place_lend with "Hplace") as "[Htok Hpart]".
    wp_op. iApply (wp_module_enter (run more) ctx_at c_ctx ctx_unset place_tok ctx_ready place_tok_once
      eq_refl eq_refl with "Hctx Htok"); [done |].
    iNext. iSplit.
    - iIntros (fields) "#Hr %Hf #Hready Htok". wp_done. iApply ("HΦ" with "Hr Hready").
      iApply (place_back with "Htok Hpart").
    - (* this thread is the one to initialise it: `currentScope = new ThreadLocal` *)
      iIntros "Hmine". wp_call.
      wp_op. iApply wp_ext_new; [done |]. iIntros "!>" (tl) "Htl".
      wp_op. iApply (wp_module_mark (run more) ctx_at c_ctx ctx_unset place_tok ctx_ready with "Hctx Hmine");
        [done | by split | done | done | done |].
      iIntros "!> Hmine".
      wp_op. iApply (wp_module_store (run more) ctx_at c_ctx ctx_unset place_tok ctx_ready with "Hctx Hmine");
        [done | by split | done | done | done | done | done |].
      iIntros "!> Hmine". iEval (cbn) in "Hmine".
      wp_done. iApply wpP_fupd.
      iMod (inv_alloc localN ⊤ (∃ s : list (tid * val), tl ↦ext (Held thread_local s) ∗
              [∗ list] e ∈ s, scope_or_null e.2)%I with "[Htl]") as "#Hlocal"; [iNext; iExists []; by iFrame |].
      iModIntro.
      wp_op. iApply (wp_module_done (run more) ctx_at c_ctx ctx_unset place_tok ctx_ready with "Hctx Hmine []");
        [done | by split | done | iExists tl; by iFrame "Hlocal" |].
      iIntros "!> Htok #Hr". wp_done. iApply ("HΦ" with "Hr [] [Htok Hpart]").
      + iExists tl. by iFrame "Hlocal".
      + iApply (place_back with "Htok Hpart").
  Qed.

  Local Opaque module_init.

End context.

(** ** `currentScope`, in a walk

    `ctx_local tl`: the walk has stopped where the code names `currentScope`; with the invariant of the object
    (`"Hctx"`) and the thread's place (`"Hplace"`, kept), the object is named and its field read: what follows
    has the thread local `tl` and its invariant (`"Hlocal"`). *)
Tactic Notation "ctx_local" ident(tl) :=
  try iClear "Hc Hlocal";
  wp_whd; wp_leaf; iApply (ctx_named with "Hctx Hplace");
  let cf := fresh "cfields" in
  iIntros (cf) "#Hc #Hready Hplace";
  iDestruct "Hready" as (tl) "[[% %] #Hlocal]";
  wp_op; iApply wp_obj_get; iModIntro; iExists _, _, _, _; iFrame "Hc"; iSplit; [done |];
  iIntros "!> _ !>"; wp_done.

(** `currentScope.set(v)`, with `"Hlocal"`: `known` shows that `v` is no object or a capability. *)
Ltac local_set known :=
  wp_op; iApply wp_ext_call;
  let s := fresh "s" in
  iInv "Hlocal" as (s) "[>Htl #Hs]" "Hclose"; iModIntro; iExists thread_local, s; iFrame "Htl";
  let intr := fresh "intr" in
  let choice := fresh "choice" in
  iIntros "!>" (intr choice); rewrite local_set_call; iIntros "Htl";
  iMod ("Hclose" with "[Htl]") as "_";
  [iNext; iExists _; iFrame "Htl"; iSplit; [known | iExact "Hs"] |];
  iModIntro; iClear "Hs"; clear s intr choice.

(** `currentScope.get()` by thread `t`, with `"Hlocal"`: what follows has the value `v`, and what it is as `H`. *)
Tactic Notation "local_get" constr(t) ident(v) constr(H) :=
  wp_op; iApply wp_ext_call;
  let s := fresh "s" in
  iInv "Hlocal" as (s) "[>Htl #Hs]" "Hclose"; iModIntro; iExists thread_local, s; iFrame "Htl";
  let intr := fresh "intr" in
  let choice := fresh "choice" in
  iIntros "!>" (intr choice); rewrite local_get_call; iIntros "Htl";
  iDestruct (local_of s t with "Hs") as "#Hgot";
  iMod ("Hclose" with "[Htl]") as "_"; [iNext; iExists s; by iFrame "Htl Hs" |];
  iModIntro; iClear "Hs"; iRevert "Hgot"; generalize (of_thread s t); intros v; iIntros "#Hgot";
  iRename "Hgot" into H; clear s intr choice.
