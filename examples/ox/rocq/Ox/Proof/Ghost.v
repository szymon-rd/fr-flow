(** What the proofs about Ox's scopes keep beside the machine's state, and the rules a proof of Ox's code uses.

    Kept, in an invariant: the steps of the system of scopes that the program has taken so far (`Places.v`),
    the place of each thread, and for each scope the set of threads its herd holds, which has every fork of
    the scope that is not past its body. A thread owns its place (`place_is`); that a step was taken is a fact
    from then on (`took`).

    A rule here is one operation on a herd's set together with the step of the system it is: adding a thread
    is a fork made, a thread taking itself out is a fork past its body, the owner finding the set empty is the
    scope ended and left. A proof of Ox's code uses these and never opens the invariant itself. *)

From iris.algebra Require Import gmap.
From iris.base_logic.lib Require Import ghost_map mono_list invariants.
From iris.proofmode Require Import proofmode.
From FrFlow.Scala Require Export Logic Sets.
Require Export FrFlowGen.OxScopes.Domain Proofs.OxScopes.Lemmas.
From Ox.Proof Require Export Moves.
Require Import Proofs.OxScopes.noForkActsAfterItsScopeIsLeft.

Class scopesGpreS (Σ : gFunctors) := ScopesGpreS {
  #[global] scopes_pre_places :: ghost_mapG Σ nat place;
  #[global] scopes_pre_herds :: ghost_mapG Σ nat unit;
  #[global] scopes_pre_taken :: mono_listG Step Σ }.

Class scopesGS (Σ : gFunctors) := ScopesGS {
  #[global] scopes_placesG :: ghost_mapG Σ nat place;
  #[global] scopes_herdsG :: ghost_mapG Σ nat unit;
  #[global] scopes_takenG :: mono_listG Step Σ;
  scopes_places : gname;
  scopes_herds : gname;
  scopes_taken : gname }.

Definition scopesΣ : gFunctors := #[ghost_mapΣ nat place; ghost_mapΣ nat unit; mono_listΣ Step].
Global Instance subG_scopesΣ {Σ} : subG scopesΣ Σ → scopesGpreS Σ.
Proof. solve_inG. Qed.

Definition scopesN : namespace := nroot .@ "scopes".

(** A herd's set holds threads only. *)
Definition all_threads (held : list val) : Prop := ∀ x, In x held → ∃ u : nat, x = VTid u.

Section ghost.
  Context `{!jvmGS code obj Σ, !scopesGS Σ}.

  Definition place_is (w : nat) (pl : place) : iProp Σ := ghost_map_elem scopes_places w (DfracOwn 1) pl.
  Definition scope_at (q : nat) : iProp Σ := ghost_map_elem scopes_herds q DfracDiscarded ().
  Definition took (e : Step) : iProp Σ := ∃ l, mono_list_lb_own scopes_taken l ∗ ⌜In e l⌝.

  Definition sets (taken : list Step) (herds : gmap nat unit) : iProp Σ :=
    [∗ map] q ↦ _ ∈ herds, ∃ held : list val,
      q ↦ext (Held concurrent_set held) ∗ ⌜set_ok taken q held ∧ all_threads held⌝.

  Definition scopes_body : iProp Σ :=
    ∃ (taken : list Step) (places : gmap nat place) (herds : gmap nat unit),
      ⌜agrees taken places (dom herds)⌝ ∗ mono_list_auth_own scopes_taken (DfracOwn 1) taken ∗
      ghost_map_auth scopes_places (DfracOwn 1) places ∗ ghost_map_auth scopes_herds (DfracOwn 1) herds ∗
      ([∗ set] w ∈ dom places, Wp.made w) ∗ sets taken herds.

  Definition scopes_inv : iProp Σ := inv scopesN scopes_body.

  Global Instance took_persistent e : Persistent (took e).
  Proof. apply _. Qed.

  (** One scope's set taken out of the rest, and put back after a step. *)
  Lemma sets_pick taken herds q :
    herds !! q = Some () →
    sets taken herds -∗
    ∃ held : list val, q ↦ext (Held concurrent_set held) ∗ ⌜set_ok taken q held ∧ all_threads held⌝ ∗
      ∀ taken' (held' : list val), q ↦ext (Held concurrent_set held') -∗
        ⌜set_ok taken' q held' ∧ all_threads held'⌝ -∗
        ⌜∀ q' h, q' ≠ q → set_ok taken q' h → set_ok taken' q' h⌝ -∗ sets taken' herds.
  Proof.
    iIntros (Hq) "Hsets". unfold sets.
    iDestruct (big_sepM_delete _ _ q with "Hsets") as "[Hset Hsets]"; [exact Hq |].
    iDestruct "Hset" as (held) "[Hext %Hset]". iExists held. iFrame "Hext". iSplit; [done |].
    iIntros (taken' held') "Hext %Hset' %Hrest". iApply (big_sepM_delete _ _ q); [exact Hq |].
    iSplitL "Hext"; [iExists held'; by iFrame |].
    iApply (big_sepM_impl with "Hsets"). iIntros "!>" (q' [] Hq') "H". iDestruct "H" as (h) "[H [%Hs %Ht]]".
    iExists h. iFrame "H". iPureIntro. split; [| exact Ht]. apply Hrest; [| exact Hs].
    intros ->. by rewrite lookup_delete_eq in Hq'.
  Qed.

  (** ** A scope opened: by a thread not past its body, over a set just made *)

  Lemma scopes_open E w r stack q :
    ↑scopesN ⊆ E → r ≠ Past →
    scopes_inv -∗ place_is w (r, stack) -∗ q ↦ext (Held concurrent_set ([] : list val)) ={E}=∗
    place_is w (r, q :: stack) ∗ scope_at q.
  Proof.
    iIntros (HE Hr) "#Hinv Hw Hq". iInv "Hinv" as ">H" "Hclose".
    iDestruct "H" as (taken places herds) "(%Ha & Ht & Hp & Hh & Hmade & Hsets)".
    iDestruct (ghost_map_lookup with "Hp Hw") as %Hw.
    iAssert ⌜herds !! q = None⌝%I as %Hfresh.
    { destruct (herds !! q) as [[] |] eqn:E'; [| done].
      iDestruct (big_sepM_lookup with "Hsets") as (held) "[Hq' _]"; [exact E' |].
      iDestruct (ext_at_once with "Hq Hq'") as %[]. }
    destruct (agrees_open taken places (dom herds) w r stack q Ha Hw Hr) as (Ha' & Hnew & Hold);
      [by apply not_elem_of_dom |].
    iMod (mono_list_auth_own_update_app [Step_Open (zt w) (zs q) (opened_inside r stack)] with "Ht") as "[Ht _]".
    iMod (ghost_map_update (r, q :: stack) with "Hp Hw") as "[Hp Hw]".
    iMod (ghost_map_insert_persist q () with "Hh") as "[Hh #Hq']"; [exact Hfresh |].
    iMod ("Hclose" with "[-Hw]") as "_"; [| by iFrame "Hw Hq'"].
    iNext. iExists _, _, _. iFrame "Ht Hp Hh". iSplit; [iPureIntro; by rewrite dom_insert_L |].
    iSplitL "Hmade"; [rewrite dom_insert_lookup_L; [done | by eexists] |].
    unfold sets. iApply big_sepM_insert; [exact Hfresh |]. iSplitL "Hq".
    { iExists []. iFrame "Hq". iPureIntro. split; [exact Hnew | by intros x []]. }
    iApply (big_sepM_impl with "Hsets"). iIntros "!>" (q' [] Hq') "H". iDestruct "H" as (h) "[H [%Hs %Ht]]".
    iExists h. iFrame "H". iPureIntro. split; [by apply Hold | exact Ht].
  Qed.

  (** ** The first root, as a proof of code meets it: after a scope is left, no thread is a fork of it not past
      its body. Were one, it could act, and by the root no fork of a scope left acts. *)

  Lemma left_no_fork E w q t stack :
    ↑scopesN ⊆ E →
    scopes_inv -∗ took (Step_Leave (zt w) (zs q)) -∗ place_is t (ForkIn q, stack) ={E}=∗ False.
  Proof.
    iIntros (HE) "#Hinv #Hleft Ht". iDestruct "Hleft" as (l) "[Hlb %Hin]".
    iInv "Hinv" as ">H" "Hclose". iDestruct "H" as (taken places herds) "(%Ha & Hauth & Hp & _)".
    iDestruct (ghost_map_lookup with "Hp Ht") as %Ht.
    iDestruct (mono_list_auth_lb_own_valid with "Hauth Hlb") as %[_ [rest ->]].
    iExFalso. iPureIntro. apply in_split in Hin as (before & between & ->).
    apply (noForkActsAfterItsScopeIsLeft_Proofs_complete _ none none_is_sound
             (agrees_act _ _ _ _ _ _ Ha Ht) before (zt w) (zs q) (between ++ rest) (zt t) nil).
    by rewrite -!app_assoc.
  Qed.

  Context (interp : code → val → Machine.P code obj (Machine.res code obj)).
  Local Instance ghost_irisGS : irisGS (jvm interp) Σ := jvm_irisGS interp.

  (** ** A fork made: a thread added to a scope's set, by a thread that has the scope open or is a fork of it *)

  Lemma wp_set_add t q r stack c E Φ :
    ↑scopesN ⊆ E → (r = ForkIn q ∨ In q stack) →
    scopes_inv -∗ scope_at q -∗ place_is t (r, stack) -∗ Wp.made c -∗
    ▷ (∀ b, place_is t (r, stack) -∗ place_is c (ForkIn q, []) -∗ Φ (inr (VBool b))) -∗
    wpP interp t (Vis (ExtCall q "add" [VTid c]) Ret) E Φ.
  Proof.
    iIntros (HE Hin) "#Hinv #Hq Hw Hc HΦ". iApply wp_ext_call. iInv "Hinv" as ">H" "Hclose".
    iDestruct "H" as (taken places herds) "(%Ha & Ht & Hp & Hh & Hmade & Hsets)".
    iDestruct (ghost_map_lookup with "Hp Hw") as %Hw. iDestruct (ghost_map_lookup with "Hh Hq") as %Hq.
    iAssert ⌜places !! c = None⌝%I as %Hc.
    { destruct (places !! c) eqn:E'; [| done].
      iDestruct (big_sepS_elem_of _ _ c with "Hmade") as "Hc'"; [apply elem_of_dom; eauto |].
      iDestruct (made_once with "Hc Hc'") as %[]. }
    iDestruct (sets_pick with "Hsets") as (held) "(Hext & [%Hset %Hall] & Hback)"; [exact Hq |].
    iModIntro. iExists concurrent_set, held. iFrame "Hext". iIntros "!>" (intr choice).
    destruct (set_add t intr held (VTid c) choice) as (b & held' & -> & Hheld'). iIntros "Hext".
    destruct (agrees_forks taken places (dom herds) t r stack q c Ha Hw Hin Hc) as [Ha' Hsets'].
    iMod (mono_list_auth_own_update_app [Step_Forks (zt t) (zs q) (zt c)] with "Ht") as "[Ht _]".
    iMod (ghost_map_insert c (ForkIn q, []) with "Hp") as "[Hp Hcp]"; [exact Hc |].
    iMod ("Hclose" with "[-HΦ Hw Hcp]") as "_"; [| iModIntro; iApply ("HΦ" with "Hw Hcp")].
    iNext. iExists _, _, herds. iFrame "Ht Hp Hh". iSplit; [done |]. iSplitL "Hmade Hc".
    { rewrite dom_insert_L. iApply big_sepS_insert; [by apply not_elem_of_dom |]. iFrame. }
    iApply ("Hback" with "Hext"); iPureIntro.
    - split.
      + apply (Hsets' q held held' Hset); [intros x Hx; apply Hheld'; by left | intros _; apply Hheld'; by right].
      + intros x [Hx | ->]%Hheld'; [by apply Hall | by exists c].
    - intros q' h Hne Hs. by apply (Hsets' q' h h Hs).
  Qed.

  (** ** A fork past its body: a thread with no scope open takes itself out of its scope's set *)

  Lemma wp_set_remove t q E Φ :
    ↑scopesN ⊆ E →
    scopes_inv -∗ scope_at q -∗ place_is t (ForkIn q, []) -∗
    ▷ (∀ b, place_is t (Past, []) -∗ Φ (inr (VBool b))) -∗
    wpP interp t (Vis (ExtCall q "remove" [VTid t]) Ret) E Φ.
  Proof.
    iIntros (HE) "#Hinv #Hq Hw HΦ". iApply wp_ext_call. iInv "Hinv" as ">H" "Hclose".
    iDestruct "H" as (taken places herds) "(%Ha & Ht & Hp & Hh & Hmade & Hsets)".
    iDestruct (ghost_map_lookup with "Hp Hw") as %Hw. iDestruct (ghost_map_lookup with "Hh Hq") as %Hq.
    iDestruct (sets_pick with "Hsets") as (held) "(Hext & [%Hset %Hall] & Hback)"; [exact Hq |].
    iModIntro. iExists concurrent_set, held. iFrame "Hext". iIntros "!>" (intr choice).
    destruct (set_remove t intr held (VTid t) choice) as (b & held' & -> & Hheld'). iIntros "Hext".
    destruct (agrees_finish taken places (dom herds) t q Ha Hw) as [Ha' Hsets'].
    iMod (mono_list_auth_own_update_app [Step_Finish (zt t)] with "Ht") as "[Ht _]".
    iMod (ghost_map_update (Past, []) with "Hp Hw") as "[Hp Hw]".
    iMod ("Hclose" with "[-HΦ Hw]") as "_"; [| iModIntro; iApply ("HΦ" with "Hw")].
    iNext. iExists _, _, herds. iFrame "Ht Hp Hh". iSplit; [done |].
    iSplitL "Hmade"; [rewrite dom_insert_lookup_L; [done | by eexists] |].
    iApply ("Hback" with "Hext"); iPureIntro.
    - split.
      + apply (Hsets' q held held' Hset). intros x Hx Hne. by apply Hheld'.
      + intros x [Hx _]%Hheld'. by apply Hall.
    - intros q' h Hne Hs. by apply (Hsets' q' h h Hs).
  Qed.

  (** ** A scope ended and left: the thread that has it open innermost finds its set empty *)

  Lemma wp_set_isEmpty t q r stack E Φ :
    ↑scopesN ⊆ E →
    scopes_inv -∗ scope_at q -∗ place_is t (r, q :: stack) -∗
    ▷ ((place_is t (r, stack) -∗ took (Step_Leave (zt t) (zs q)) -∗ Φ (inr (VBool true))) ∧
       (place_is t (r, q :: stack) -∗ Φ (inr (VBool false)))) -∗
    wpP interp t (Vis (ExtCall q "isEmpty" []) Ret) E Φ.
  Proof.
    iIntros (HE) "#Hinv #Hq Hw HΦ". iApply wp_ext_call. iInv "Hinv" as ">H" "Hclose".
    iDestruct "H" as (taken places herds) "(%Ha & Ht & Hp & Hh & Hmade & Hsets)".
    iDestruct (ghost_map_lookup with "Hp Hw") as %Hw. iDestruct (ghost_map_lookup with "Hh Hq") as %Hq.
    iDestruct (sets_pick with "Hsets") as (held) "(Hext & [%Hset %Hall] & Hback)"; [exact Hq |].
    iModIntro. iExists concurrent_set, held. iFrame "Hext". iIntros "!>" (intr choice).
    rewrite set_isEmpty. iIntros "Hext". destruct held as [| x held].
    - destruct (agrees_end taken places (dom herds) t r stack q Ha Hw Hset) as [Ha' Hsets'].
      iMod (mono_list_auth_own_update_app [Step_End (zt t) (zs q); Step_Leave (zt t) (zs q)] with "Ht")
        as "[Ht #Hlb]".
      iMod (ghost_map_update (r, stack) with "Hp Hw") as "[Hp Hw]".
      iMod ("Hclose" with "[-HΦ Hw]") as "_".
      { iNext. iExists _, _, herds. iFrame "Ht Hp Hh". iSplit; [done |].
        iSplitL "Hmade"; [rewrite dom_insert_lookup_L; [done | by eexists] |].
        iApply ("Hback" with "Hext"); iPureIntro; [split; [by apply Hsets' | exact Hall] |].
        intros q' h _ Hs. by apply Hsets'. }
      iModIntro. iDestruct "HΦ" as "[HΦ _]". iApply ("HΦ" with "Hw"). iExists _. iFrame "Hlb".
      iPureIntro. apply in_app_iff. right. right. by left.
    - iMod ("Hclose" with "[-HΦ Hw]") as "_".
      { iNext. iExists _, _, herds. iFrame "Ht Hp Hh Hmade". iSplit; [done |].
        iApply ("Hback" with "Hext"); by iPureIntro. }
      iModIntro. iDestruct "HΦ" as "[_ HΦ]". iApply ("HΦ" with "Hw").
  Qed.

  (** ** A set read: a call that leaves it as it is, by any thread *)

  Lemma wp_set_read t q method args E Φ :
    ↑scopesN ⊆ E →
    scopes_inv -∗ scope_at q -∗
    ▷ (∀ (held : list val) intr choice, ⌜all_threads held⌝ -∗
         ∃ y, ⌜p_call concurrent_set method t intr held args choice = Gives y held⌝ ∗ Φ y) -∗
    wpP interp t (Vis (ExtCall q method args) Ret) E Φ.
  Proof.
    iIntros (HE) "#Hinv #Hq HΦ". iApply wp_ext_call. iInv "Hinv" as ">H" "Hclose".
    iDestruct "H" as (taken places herds) "(%Ha & Ht & Hp & Hh & Hmade & Hsets)".
    iDestruct (ghost_map_lookup with "Hh Hq") as %Hq.
    iDestruct (sets_pick with "Hsets") as (held) "(Hext & [%Hset %Hall] & Hback)"; [exact Hq |].
    iModIntro. iExists concurrent_set, held. iFrame "Hext". iIntros "!>" (intr choice).
    iDestruct ("HΦ" $! held intr choice with "[//]") as (y) "[%Hcall HΦ]". rewrite Hcall. iIntros "Hext".
    iMod ("Hclose" with "[-HΦ]") as "_"; [| by iModIntro].
    iNext. iExists _, _, herds. iFrame "Ht Hp Hh Hmade". iSplit; [done |].
    iApply ("Hback" with "Hext"); by iPureIntro.
  Qed.

End ghost.
