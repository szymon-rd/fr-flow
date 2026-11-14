(** `scopedWithCapability`: a scope run. The capability's herd was made by the calling thread, which so has the
    scope open innermost. The code sets the thread's current scope, runs the body, closes the herd
    (`herd_close`: the scope is ended and left), runs the scope's finalizers, and puts the thread's scope back.

    The body is proven from the thread's place with the scope open, and gives that place back. *)

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From Ox.Proof Require Export Start.
Open Scope string_scope.

Definition c_scopes : string := "ox.unsupervised$package$".
Definition m_scoped : sym := Member c_scopes "scopedWithCapability" "1,ox.Ox,scala.Function1:java.lang.Object".
Definition c_aref : string := p_class atomic_reference.
Definition m_runFinalizers : sym :=
  Member c_scopes "runFinalizers" "1,ox.ResourceScope,scala.util.Either:java.lang.Object".

(** A function that takes arguments: one written with a parameter list. *)
Definition takes_arguments (d : tree) : Prop :=
  ∃ s flags ps pss type body overridden, d = DefDef s flags (ps :: pss) type body overridden.

Section scope.
  Context `{!jvmGS code obj Σ, !scopesGS Σ} (more : table).
  Local Instance scope_irisGS : irisGS (jvm (run more)) Σ := jvm_irisGS (run more).

  (** The capability at `r`: its herd is at `h`, its finalizers are kept at `fin`. *)
  Definition cap_at (r h fin : nat) : iProp Σ :=
    ∃ fields, r ↦obj□ (c_cap, fields) ∗
      ⌜field fields "herd" = Some (herd_at h) ∧ writer fields "herd" = None ∧
       field fields "finalizers" = Some (vext c_aref fin) ∧ writer fields "finalizers" = None⌝.

  (** ** `runFinalizers`, of a scope with no finalizer: it gives what the scope's body gave *)

  Lemma finalizers_right t r h fin v Φ :
    plain v →
    cap_at r h fin -∗ fin ↦ext (Held atomic_reference (VList [])) -∗ Φ (inr v) -∗
    wpP (run more) t (run more (Method m_runFinalizers)
      (VList [VObj (Module c_scopes); VObj (Ref c_cap r); vdata c_right [v]])) ⊤ Φ.
  Proof.
    iIntros (Hv) "#Hat Hfin HΦ". iDestruct "Hat" as (fields) "[Hr [%Hfh [%Hwh [%Hff %Hwf]]]]".
    (* scope.finalizers.getAndSet(null): none *)
    wp_call. wp_op. iApply wp_obj_get. iModIntro. iExists _, _, _, _. iFrame "Hr".
    iSplit; [done |]. iIntros "!> _ !>". wp_done.
    wp_op. iApply wp_ext_call. iModIntro. iExists atomic_reference, _. iFrame "Hfin". iIntros "!>" (intr choice).
    rewrite ref_getAndSet. iIntros "Hfin !>".
    (* the result is what the body gave *)
    wp_whd. fold (held v). rewrite (held_plain v Hv). wp_done. iApply "HΦ".
  Qed.

  (** What the scope's body threw is thrown again. *)
  Lemma finalizers_left t r h fin x Φ :
    plain (exn_value x) →
    cap_at r h fin -∗ fin ↦ext (Held atomic_reference (VList [])) -∗ Φ (inl x) -∗
    wpP (run more) t (run more (Method m_runFinalizers)
      (VList [VObj (Module c_scopes); VObj (Ref c_cap r); vdata c_left [exn_value x]])) ⊤ Φ.
  Proof.
    iIntros (Hv) "#Hat Hfin HΦ". iDestruct "Hat" as (fields) "[Hr [%Hfh [%Hwh [%Hff %Hwf]]]]".
    wp_call. wp_op. iApply wp_obj_get. iModIntro. iExists _, _, _, _. iFrame "Hr".
    iSplit; [done |]. iIntros "!> _ !>". wp_done.
    wp_op. iApply wp_ext_call. iModIntro. iExists atomic_reference, _. iFrame "Hfin". iIntros "!>" (intr choice).
    rewrite ref_getAndSet. iIntros "Hfin !>".
    wp_plain (exn_value x) Hv.
    wp_call. wp_plain (exn_value x) Hv.
    (* throw e *)
    wp_whd. fold (as_exn (exn_value x)). rewrite as_exn_value.
    wp_done. wp_done. iApply "HΦ".
  Qed.

  (** What a body may end with, for the code that runs it: a value that is plain where a name holds it; or
      an exception that is so as a value, and is a `Throwable` to the handler that takes it. *)
  Definition throwable (x : exn) : Prop :=
    instance (extend Ox more) supers (exn_value x)
      (TyAlias "scala.package$.Throwable" (TyRef "java.lang.Throwable")) = Some true.
  Definition given_back (res : res code obj) : Prop :=
    match res with
    | inr v => plain v
    | inl x => plain (exn_value x) ∧ throwable x
    end.

  Lemma scoped t n r h fin q rl stack fd fsc fgroup Φ :
    takes_arguments fd →
    ctx_inv -∗ scopes_inv -∗ is_cap n (VObj (Ref c_cap r)) -∗ cap_at r h fin -∗ is_herd h q t -∗
    place_is t (rl, q :: stack) -∗ fin ↦ext (Held atomic_reference (VList [])) -∗
    (place_is t (rl, q :: stack) -∗
       wpP (run more) t (run more (Fn fd fsc fgroup) (VList [VObj (Ref c_cap r)])) ⊤
         (λ res, place_is t (rl, q :: stack) ∗ ⌜given_back res⌝)) -∗
    (place_is t (rl, stack) -∗ took (Step_Leave (zt t) (zs q)) -∗ ∀ res, Φ res) -∗
    wpP (run more) t (run more (Method m_scoped)
      (VList [VObj (Module c_scopes); VObj (Ref c_cap r); VCode (Fn fd fsc fgroup)])) ⊤ Φ.
  Proof.
    iIntros ((fs & fflags & fps & fpss & ftype & fbody & fov & ->)) "#Hctx #Hinv #Hcap #Hat #Hherd Hplace Hfin Hbody HΦ".
    iPoseProof "Hat" as "Hat'". iDestruct "Hat'" as (fields) "[Hr [%Hfh [%Hwh [%Hff %Hwf]]]]".
    (* val previousScope = currentScope.get() *)
    ctx_local ltl. local_get t prev "Hprev". iDestruct (scope_or_null_plain with "Hprev") as %Hprev.
    iDestruct (scope_or_null_obj with "Hprev") as %[prevo ->]. wp_done.
    (* currentScope.set(capability) *)
    ctx_local ltl2. local_set ltac:(iRight; iExists n; iExact "Hcap"). wp_done.
    (* runWithCurrentScopeSet: the body *)
    wp_call. wp_whd. iApply wpP_call_then. iNext. iApply (wpP_wand with "[Hbody Hplace]"); [by iApply "Hbody" |].
    iIntros (res) "[Hplace %Hres]". destruct res as [x | v].
    (* however the body ended: capability.herd.interruptAllAndJoinUntilCompleted() *)
    all: wp_call; wp_op; iApply wp_obj_get; iModIntro; iExists _, _, _, _; iFrame "Hr".
    all: iSplit; [done |]; iIntros "!> _ !>"; wp_done.
    all: wp_call; iApply (herd_close with "Hinv Hherd Hplace"); iIntros "Hplace #Hleft"; iSplit.
    - (* the body threw, the herd closed: `catch case e: Throwable => Left(e)` *)
      destruct Hres as [Hplain Hthrowable].
      wp_whd. fold (exn_val x). rewrite exn_val_value.
      with_strategy opaque [instance] wp_whd. rewrite Hthrowable.
      wp_plain (exn_value x) Hplain.
      wp_call. iApply (finalizers_left with "Hat Hfin"); [done |].
      (* finally currentScope.set(previousScope) *)
      wp_done. wp_done. ctx_local ltl3. wp_plain (VObj prevo : val) Hprev. local_set ltac:(iExact "Hprev").
      wp_done. wp_done. wp_done. iApply ("HΦ" with "Hplace Hleft").
    - (* the body threw, and the owner was interrupted while it closed the herd *)
      wp_call. change (VExn InterruptedException) with (exn_value InterruptedException).
      iApply (finalizers_left with "Hat Hfin"); [done |].
      wp_done. wp_done. ctx_local ltl3. wp_plain (VObj prevo : val) Hprev. local_set ltac:(iExact "Hprev").
      wp_done. wp_done. wp_done. iApply ("HΦ" with "Hplace Hleft").
    - (* the body gave a value, the herd closed *)
      wp_call. iApply (finalizers_right with "Hat Hfin"); [exact Hres |].
      wp_done. wp_done. ctx_local ltl3. wp_plain (VObj prevo : val) Hprev. local_set ltac:(iExact "Hprev").
      repeat wp_done. iApply ("HΦ" with "Hplace Hleft").
    - (* the body gave a value, and the owner was interrupted while it closed the herd *)
      wp_call. change (VExn InterruptedException) with (exn_value InterruptedException).
      iApply (finalizers_left with "Hat Hfin"); [done |].
      wp_done. wp_done. ctx_local ltl3. wp_plain (VObj prevo : val) Hprev. local_set ltac:(iExact "Hprev").
      repeat wp_done. iApply ("HΦ" with "Hplace Hleft").
  Qed.

End scope.
