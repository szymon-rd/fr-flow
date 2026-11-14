(** A rule for each operation of the machine, proven from what the machine says the operation may do
    (`Machine.opstep`).

    A rule is said with the masks of an atomic step: what the operation needs may be taken out of invariants
    for the step (`|={E,E'}=>`) and is put back after it (`={E',E}=∗`). *)

From iris.algebra Require Import gmap.
From iris.program_logic Require Import lifting.
From iris.proofmode Require Import proofmode.
From FrFlow.Threads Require Import Prog.
From FrFlow.Jvm Require Export Wp.

Section rules.
  Context {code obj : Type} `{!jvmGS code obj Σ}.
  Context (interp : code → Machine.val code obj → Machine.P code obj (Machine.res code obj)).

  Abbreviation mval := (Machine.val code obj).
  Abbreviation mstate := (Machine.state code obj).
  Abbreviation prog := (Machine.P code obj).
  Abbreviation mres := (Machine.res code obj).
  Abbreviation thread := (running code obj).
  Abbreviation wpp := (wpP interp).
  Local Instance rules_irisGS : irisGS (jvm interp) Σ := jvm_irisGS interp.

  Implicit Types σ : mstate.

  (** ** The logic's account of the state, kept through each change *)

  Lemma upd_insert {B} (m : gmap nat B) (f : nat → option B) k v :
    (∀ r, m !! r = f r) → ∀ r, <[k:=v]> m !! r = upd f k (Some v) r.
  Proof.
    intros H r. unfold upd. destruct (PeanoNat.Nat.eq_dec r k) as [-> | ?].
    - rewrite lookup_insert_eq. done.
    - rewrite lookup_insert_ne; [apply H | done].
  Qed.

  Lemma interp_right σ : jvm_interp σ -∗ ⌜s_wrong σ = None⌝.
  Proof. iDestruct 1 as (mo me mt ms mz) "(_ & _ & _ & _ & _ & _ & %H)". iPureIntro. tauto. Qed.

  Lemma interp_obj σ r dq (o : Machine.object code obj) : jvm_interp σ -∗ r ↦obj{dq} o -∗ ⌜s_obj σ r = Some o⌝.
  Proof.
    iDestruct 1 as (mo me mt ms mz) "(Ho & _ & _ & _ & _ & _ & %H)". iIntros "Hr".
    iDestruct (ghost_map_lookup with "Ho Hr") as %E. iPureIntro. destruct H as (Hmo & _). by rewrite -Hmo.
  Qed.

  Lemma interp_obj_set σ r (o o' : Machine.object code obj) :
    jvm_interp σ -∗ r ↦obj o ==∗ jvm_interp (set_obj σ r o') ∗ r ↦obj o'.
  Proof.
    iDestruct 1 as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)". iIntros "Hr".
    iMod (ghost_map_update o' with "Ho Hr") as "[Ho $]". iModIntro.
    iExists _, me, mt, ms, mz. iFrame. iPureIntro. destruct H as (Hmo & H). split; [| exact H].
    by apply upd_insert.
  Qed.

  Lemma interp_obj_new σ r (o : Machine.object code obj) :
    s_obj σ r = None → jvm_interp σ ==∗ jvm_interp (set_obj σ r o) ∗ r ↦obj o.
  Proof.
    iIntros (Hr). iDestruct 1 as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)".
    destruct H as (Hmo & H).
    iMod (ghost_map_insert r o with "Ho") as "[Ho $]"; [by rewrite Hmo |]. iModIntro.
    iExists _, me, mt, ms, mz. iFrame. iPureIntro. split; [by apply upd_insert | exact H].
  Qed.

  Lemma interp_ext σ r dq (h : Machine.held code obj) : jvm_interp σ -∗ r ↦ext{dq} h -∗ ⌜s_ext σ r = Some h⌝.
  Proof.
    iDestruct 1 as (mo me mt ms mz) "(_ & He & _ & _ & _ & _ & %H)". iIntros "Hr".
    iDestruct (ghost_map_lookup with "He Hr") as %E. iPureIntro. destruct H as (_ & Hme & _). by rewrite -Hme.
  Qed.

  Lemma interp_ext_set σ r (h h' : Machine.held code obj) :
    jvm_interp σ -∗ r ↦ext h ==∗ jvm_interp (set_ext σ r h') ∗ r ↦ext h'.
  Proof.
    iDestruct 1 as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)". iIntros "Hr".
    iMod (ghost_map_update h' with "He Hr") as "[He $]". iModIntro.
    iExists mo, _, mt, ms, mz. iFrame. iPureIntro. destruct H as (Hmo & Hme & H).
    split; [exact Hmo |]. split; [by apply upd_insert | exact H].
  Qed.

  Lemma interp_ext_new σ r (h : Machine.held code obj) :
    s_ext σ r = None → jvm_interp σ ==∗ jvm_interp (set_ext σ r h) ∗ r ↦ext h.
  Proof.
    iIntros (Hr). iDestruct 1 as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)".
    destruct H as (Hmo & Hme & H).
    iMod (ghost_map_insert r h with "He") as "[He $]"; [by rewrite Hme |]. iModIntro.
    iExists mo, _, mt, ms, mz. iFrame. iPureIntro. split; [exact Hmo |]. split; [by apply upd_insert | exact H].
  Qed.

  (** A change to a thread that leaves what it runs and where it is in its life: its interrupt status. *)
  Lemma interp_same σ u th th' :
    s_th σ u = Some th → t_code th' = t_code th → t_status th' = t_status th →
    jvm_interp σ -∗ jvm_interp (set_th σ u th').
  Proof.
    iIntros (Hu Hc Hs). iDestruct 1 as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)".
    iExists mo, me, mt, ms, mz. iFrame. iPureIntro.
    destruct H as (Hmo & Hme & Hmt & Hms & Hmz & Hw). repeat split; try done.
    - intros r. rewrite Hmt. simpl. unfold upd. destruct (PeanoNat.Nat.eq_dec r u) as [-> |]; [| done].
      rewrite Hu. simpl. by rewrite Hc Hs.
    - intros r Hr. specialize (Hms r Hr). unfold begun in *. simpl. unfold upd.
      destruct (PeanoNat.Nat.eq_dec r u) as [-> |]; [| done]. rewrite Hu in Hms. destruct th, th'; simpl in *. by subst.
    - intros Hr. apply Hmz in Hr. unfold over in *. simpl. unfold upd.
      destruct (PeanoNat.Nat.eq_dec u0 u) as [-> |]; [| done]. rewrite Hu in Hr. destruct th, th'; simpl in *. by subst.
    - intros Hr. apply Hmz. unfold over in *. simpl in Hr. unfold upd in Hr.
      destruct (PeanoNat.Nat.eq_dec u0 u) as [-> |]; [| done]. rewrite Hu. destruct th, th'; simpl in *. by subst.
  Qed.

  Lemma interp_clear σ t : jvm_interp σ -∗ jvm_interp (clear_intr σ t).
  Proof.
    unfold clear_intr. destruct (s_th σ t) as [th |] eqn:E; [| by iIntros "$"].
    by iApply interp_same.
  Qed.

  (** ** The program's objects *)

  Lemma wp_obj_new t cls fields E Φ :
    ▷ (∀ r, r ↦obj (cls, fields) -∗ Φ (inr r)) ⊢ wpp t (Vis (ObjNew cls fields) Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' (r & Hr & -> & ->)).
    iMod (interp_obj_new _ r (cls, fields) with "Hσ") as "[$ Hr]"; [done |].
    iMod "Hclose" as "_". iModIntro. simpl. iSplit; [done |]. by iApply "HΦ".
  Qed.

  Lemma wp_obj_get t r name E E' Φ :
    (|={E,E'}=> ∃ dq cls fields v, r ↦obj{dq} (cls, fields) ∗ ⌜field fields name = Some v⌝ ∗
        ▷ (r ↦obj{dq} (cls, fields) ={E',E}=∗ Φ (inr v)))
    ⊢ wpp t (Vis (ObjGet r name) Ret) E Φ.
  Proof.
    iIntros "H". iApply wpP_op. iIntros (σ) "Hσ". iMod "H" as (dq cls fields v) "(Hr & %Hf & HΦ)".
    iDestruct (interp_obj with "Hσ Hr") as %Ho.
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop).
    simpl in Hop. rewrite Ho Hf in Hop. destruct Hop as [-> ->].
    iMod "Hclose" as "_". iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl. by iFrame.
  Qed.

  Lemma wp_obj_set t r name v E E' Φ :
    (|={E,E'}=> ∃ cls fields, r ↦obj (cls, fields) ∗
        ▷ (r ↦obj (cls, with_field fields name v) ={E',E}=∗ Φ (inr tt)))
    ⊢ wpp t (Vis (ObjSet r name v) Ret) E Φ.
  Proof.
    iIntros "H". iApply wpP_op. iIntros (σ) "Hσ". iMod "H" as (cls fields) "(Hr & HΦ)".
    iDestruct (interp_obj with "Hσ Hr") as %Ho.
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop).
    simpl in Hop. rewrite Ho in Hop. destruct Hop as [-> ->].
    iMod (interp_obj_set _ _ _ (cls, with_field fields name v) with "Hσ Hr") as "[$ Hr]".
    iMod "Hclose" as "_". iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl. by iFrame.
  Qed.

  Lemma wp_obj_class t r E E' Φ :
    (|={E,E'}=> ∃ dq cls fields, r ↦obj{dq} (cls, fields) ∗ ▷ (r ↦obj{dq} (cls, fields) ={E',E}=∗ Φ (inr cls)))
    ⊢ wpp t (Vis (ObjClass r) Ret) E Φ.
  Proof.
    iIntros "H". iApply wpP_op. iIntros (σ) "Hσ". iMod "H" as (dq cls fields) "(Hr & HΦ)".
    iDestruct (interp_obj with "Hσ Hr") as %Ho.
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop).
    simpl in Hop. rewrite Ho in Hop. destruct Hop as [-> ->].
    iMod "Hclose" as "_". iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl. by iFrame.
  Qed.

  (** What one thread at a time does: by who holds the object, and what the object says of it. *)
  Lemma wp_enter t r name what E E' Φ :
    (|={E,E'}=> ∃ cls fields, r ↦obj (cls, fields) ∗
       ▷ match field fields name, holder fields name with
         | Some v, _ => r ↦obj (cls, fields) ={E',E}=∗ Φ (inr (Some v))
         | None, None =>
             r ↦obj (cls, with_field fields (entered name) (VTid t)) ={E',E}=∗ Φ (inr None)
         | None, Some u => r ↦obj (cls, fields) ={E',E}=∗
             match what with
             | OfMember => Φ (inl InterruptedException)
             | OfMethod => ⌜u = t⌝ → Φ (inr None)
             | OfClass => ⌜u = t⌝ → Φ (inr (Some VUnit))
             end
         end)
    ⊢ wpp t (Vis (Enter r name what) Ret) E Φ.
  Proof.
    iIntros "H". iApply wpP_op. iIntros (σ) "Hσ". iMod "H" as (cls fields) "(Hr & HΦ)".
    iDestruct (interp_obj with "Hσ Hr") as %Ho.
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop).
    simpl in Hop. rewrite Ho in Hop. iMod "Hclose" as "_".
    destruct (field fields name) as [v |].
    - destruct Hop as [-> ->]. iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl. by iFrame.
    - destruct (holder fields name) as [u |].
      + destruct what.
        * destruct Hop as (-> & _ & ->). iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl.
          iSplitL "Hσ"; [by iApply interp_clear |]. by iSplit.
        * destruct Hop as (-> & -> & ->). iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl.
          iFrame "Hσ". iSplit; [done |]. by iApply "HΦ".
        * destruct Hop as (-> & -> & ->). iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl.
          iFrame "Hσ". iSplit; [done |]. by iApply "HΦ".
      + destruct Hop as [-> ->].
        iMod (interp_obj_set _ _ _ (cls, with_field fields (entered name) (VTid t)) with "Hσ Hr") as "[$ Hr]".
        iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl. by iFrame.
  Qed.

  (** ** An object of a class from outside: by its protocol *)

  Lemma wp_ext_new t (p : Machine.protocol code obj) args s E Φ :
    p_new p args = Some s →
    ▷ (∀ r, r ↦ext (Held p s) -∗ Φ (inr r)) ⊢ wpp t (Vis (ExtNew p args) Ret) E Φ.
  Proof.
    iIntros (Hnew) "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop).
    simpl in Hop. rewrite Hnew in Hop. destruct Hop as (r & Hr & -> & ->).
    iMod (interp_ext_new _ r (Held p s) with "Hσ") as "[$ Hr]"; [done |].
    iMod "Hclose" as "_". iModIntro. simpl. iSplit; [done |]. by iApply "HΦ".
  Qed.

  (** A method: whatever the protocol says the call gives, for any choice the class makes and whether or not
      the caller is interrupted, what follows has what it needs; a call that waits may only end interrupted. *)
  Lemma wp_ext_call t r method args E E' Φ :
    (|={E,E'}=> ∃ (p : Machine.protocol code obj) (s : p_state p), r ↦ext (Held p s) ∗
       ▷ ∀ intr choice,
           match p_call p method t intr s args choice with
           | Gives y s' => r ↦ext (Held p s') ={E',E}=∗ Φ y
           | Waits | Interrupted => r ↦ext (Held p s) ={E',E}=∗ Φ (inl InterruptedException)
           | Unknown => False
           end)
    ⊢ wpp t (Vis (ExtCall r method args) Ret) E Φ.
  Proof.
    iIntros "H". iApply wpP_op. iIntros (σ) "Hσ". iMod "H" as (p s) "(Hr & HΦ)".
    iDestruct (interp_ext with "Hσ Hr") as %He.
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop).
    simpl in Hop. rewrite He in Hop. destruct Hop as (choice & Hop). iMod "Hclose" as "_".
    iSpecialize ("HΦ" $! (interrupted σ t) choice).
    destruct (p_call p method t (interrupted σ t) s args choice) as [y s' | | |].
    - destruct Hop as [-> ->]. iMod (interp_ext_set _ _ _ (Held p s') with "Hσ Hr") as "[$ Hr]".
      iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl. by iFrame.
    - destruct Hop as (-> & _ & ->). iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl.
      iSplitL "Hσ"; [by iApply interp_clear |]. by iSplit.
    - destruct Hop as (-> & ->). iMod ("HΦ" with "Hr") as "HΦ". iModIntro. simpl.
      iSplitL "Hσ"; [by iApply interp_clear |]. by iSplit.
    - done.
  Qed.

  (** A program with no meaning has no rule: it is passed only where it cannot be reached. *)

  (** ** Threads *)

  Lemma interp_thread σ u c s :
    jvm_interp σ -∗ thread_is u c s -∗ ⌜∃ i, s_th σ u = Some (Thread c s i)⌝.
  Proof.
    iDestruct 1 as (mo me mt ms mz) "(_ & _ & Ht & _ & _ & _ & %H)". iIntros "Hu".
    iDestruct (ghost_map_lookup with "Ht Hu") as %E. iPureIntro.
    destruct H as (_ & _ & Hmt & _). rewrite Hmt in E.
    destruct (s_th σ u) as [[c' s' i] |]; simpl in E; [| done]. injection E as -> ->. by exists i.
  Qed.

  Lemma wp_current_thread t E Φ : ▷ Φ (inr t) ⊢ wpp t (Vis CurrentThread Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' [-> ->]).
    iMod "Hclose" as "_". iModIntro. simpl. by iFrame.
  Qed.

  (** Operations that leave the state, or only the caller's interrupt status, and may end interrupted. *)
  Lemma wp_thread_sleep t E Φ :
    ▷ (Φ (inr tt) ∧ Φ (inl InterruptedException)) ⊢ wpp t (Vis ThreadSleep Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop). iMod "Hclose" as "_". iModIntro.
    destruct Hop as [[-> ->] | (-> & _ & ->)]; simpl.
    - iFrame. iSplit; [done |]. by iDestruct "HΦ" as "[$ _]".
    - iSplitL "Hσ"; [by iApply interp_clear |]. iSplit; [done |]. by iDestruct "HΦ" as "[_ $]".
  Qed.

  Lemma wp_thread_interrupted t E Φ : ▷ (∀ b, Φ (inr b)) ⊢ wpp t (Vis ThreadInterrupted Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' [-> ->]).
    iMod "Hclose" as "_". iModIntro. simpl. iSplitL "Hσ"; [by iApply interp_clear |]. iSplit; [done |]. iApply "HΦ".
  Qed.

  Lemma wp_thread_yield t E Φ : ▷ Φ (inr tt) ⊢ wpp t (Vis ThreadYield Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' [-> ->]).
    iMod "Hclose" as "_". iModIntro. simpl. by iFrame.
  Qed.

  Lemma wp_park t E Φ : ▷ Φ (inr tt) ⊢ wpp t (Vis Park Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' [-> ->]).
    iMod "Hclose" as "_". iModIntro. simpl. by iFrame.
  Qed.

  Lemma wp_nano_time t E Φ : ▷ (∀ z, Φ (inr z)) ⊢ wpp t (Vis NanoTime Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' (z & -> & ->)).
    iMod "Hclose" as "_". iModIntro. simpl. iFrame. iSplit; [done |]. iApply "HΦ".
  Qed.

  Lemma wp_thread_interrupt t u E Φ : ▷ Φ (inr tt) ⊢ wpp t (Vis (ThreadInterrupt u) Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' [-> Hσ']).
    iMod "Hclose" as "_". iModIntro. simpl. iFrame "HΦ".
    destruct (s_th σ u) as [[c s i] |] eqn:Eu; [| by subst].
    destruct s; [destruct Hσ' as [-> | ->]; [| done] | subst | destruct Hσ' as [-> | ->]; [| done]];
      by iApply (interp_same with "Hσ").
  Qed.

  (** ** A thread's life: made, started, ended *)

  Lemma status_upd (mt : gmap tid (code * tstatus)) σ u th :
    (∀ r, mt !! r = status_of (s_th σ r)) →
    ∀ r, <[u:=(t_code th, t_status th)]> mt !! r = status_of (s_th (set_th σ u th) r).
  Proof.
    intros H r. simpl. unfold upd. destruct (PeanoNat.Nat.eq_dec r u) as [-> | ?].
    - by rewrite lookup_insert_eq.
    - rewrite lookup_insert_ne; [apply H | done].
  Qed.

  Lemma interp_thread_new σ u c :
    s_th σ u = None → jvm_interp σ ==∗ jvm_interp (set_th σ u (Thread c TNew false)) ∗ thread_is u c TNew.
  Proof.
    iIntros (Hu). iDestruct 1 as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)".
    destruct H as (Hmo & Hme & Hmt & Hms & Hmz & Hw).
    iMod (ghost_map_insert u (c, TNew) with "Ht") as "[Ht $]"; [by rewrite Hmt Hu |]. iModIntro.
    iExists mo, me, _, ms, mz. iFrame. iPureIntro. repeat split; try done.
    - apply (status_upd mt σ u (Thread c TNew false)), Hmt.
    - intros r Hr. specialize (Hms r Hr). unfold begun in *. simpl. unfold upd.
      destruct (PeanoNat.Nat.eq_dec r u) as [-> |]; [| done]. by rewrite Hu in Hms.
    - intros Hr. apply Hmz in Hr. unfold over in *. simpl. unfold upd.
      destruct (PeanoNat.Nat.eq_dec u0 u) as [-> |]; [| done]. by rewrite Hu in Hr.
    - intros Hr. apply Hmz. unfold over in *. simpl in Hr. unfold upd in Hr.
      by destruct (PeanoNat.Nat.eq_dec u0 u) as [-> |].
  Qed.

  Lemma interp_thread_start σ u c i :
    s_th σ u = Some (Thread c TNew i) →
    jvm_interp σ -∗ thread_is u c TNew ==∗
    jvm_interp (set_th σ u (Thread c TStarted i)) ∗ thread_is u c TStarted ∗ started u.
  Proof.
    iIntros (Hu). iDestruct 1 as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)". iIntros "Hth".
    destruct H as (Hmo & Hme & Hmt & Hms & Hmz & Hw).
    iMod (ghost_map_update (c, TStarted) with "Ht Hth") as "[Ht $]".
    assert (ms !! u = None) as Hnone.
    { destruct (ms !! u) eqn:E; [| done]. assert (begun σ u) as Hb by (apply Hms; eauto).
      unfold begun in Hb. by rewrite Hu in Hb. }
    iMod (ghost_map_insert_persist u () with "Hs") as "[Hs $]"; [done |]. iModIntro.
    iExists mo, me, _, _, mz. iFrame. iPureIntro. repeat split; try done.
    - apply (status_upd mt σ u (Thread c TStarted i)), Hmt.
    - intros r Hr. unfold begun. simpl. unfold upd. destruct (PeanoNat.Nat.eq_dec r u) as [-> |]; [done |].
      apply Hms. by rewrite lookup_insert_ne in Hr.
    - intros Hr. apply Hmz in Hr. unfold over in *. simpl. unfold upd.
      destruct (PeanoNat.Nat.eq_dec u0 u) as [-> |]; [| done]. by rewrite Hu in Hr.
    - intros Hr. apply Hmz. unfold over in *. simpl in Hr. unfold upd in Hr.
      by destruct (PeanoNat.Nat.eq_dec u0 u) as [-> |].
  Qed.

  Lemma interp_thread_exit σ t c :
    jvm_interp σ -∗ thread_is t c TStarted ==∗ jvm_interp (terminate σ t) ∗ ended t.
  Proof.
    iIntros "Hσ Hth". iDestruct (interp_thread with "Hσ Hth") as %(i & Hu).
    iDestruct "Hσ" as (mo me mt ms mz) "(Ho & He & Ht & Hs & Hz & Hzs & %H)".
    destruct H as (Hmo & Hme & Hmt & Hms & Hmz & Hw).
    iMod (ghost_map_update (c, TTerminated) with "Ht Hth") as "[Ht _]".
    assert (mz !! t = None) as Hnone.
    { destruct (mz !! t) eqn:E; [| done]. assert (over σ t) as Hb by (apply Hmz; eauto).
      unfold over in Hb. by rewrite Hu in Hb. }
    iMod (ghost_map_insert_persist t () with "Hz") as "[Hz #Hended]"; [done |]. iModIntro.
    iFrame "Hended". unfold terminate. rewrite Hu. simpl.
    iExists mo, me, _, ms, _. iFrame. iSplit; [by iApply big_sepM_insert; [done | iFrame "#"] |].
    iPureIntro. repeat split; try done.
    - apply (status_upd mt σ t (Thread c TTerminated i)), Hmt.
    - intros r Hr. specialize (Hms r Hr). unfold begun in *. simpl. unfold upd.
      by destruct (PeanoNat.Nat.eq_dec r t) as [-> |].
    - intros Hr. unfold over. simpl. unfold upd. destruct (PeanoNat.Nat.eq_dec u t) as [-> |]; [done |].
      apply Hmz. by rewrite lookup_insert_ne in Hr.
    - intros Hr. unfold over in Hr. simpl in Hr. unfold upd in Hr.
      destruct (PeanoNat.Nat.eq_dec u t) as [-> |]; [by rewrite lookup_insert_eq |].
      rewrite lookup_insert_ne; [by apply Hmz | done].
  Qed.

  Lemma interp_ended σ u : over σ u → jvm_interp σ -∗ ended u.
  Proof.
    iIntros (Ho). iDestruct 1 as (mo me mt ms mz) "(_ & _ & _ & _ & _ & Hzs & %H)".
    destruct H as (_ & _ & _ & _ & Hmz & _). apply Hmz in Ho as [[] Ho].
    by iDestruct (big_sepM_lookup with "Hzs") as "$".
  Qed.

  Lemma interp_started σ u : jvm_interp σ -∗ started u -∗ ⌜begun σ u⌝.
  Proof.
    iDestruct 1 as (mo me mt ms mz) "(_ & _ & _ & Hs & _ & _ & %H)". iIntros "Hu".
    iDestruct (ghost_map_lookup with "Hs Hu") as %E. iPureIntro.
    destruct H as (_ & _ & _ & Hms & _). apply Hms. eauto.
  Qed.

  Lemma wp_new_thread t c E Φ :
    ▷ (∀ u, thread_is u c TNew -∗ Φ (inr u)) ⊢ wpp t (Vis (NewThread c) Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' (u & Hu & -> & ->)).
    iMod (interp_thread_new _ u c with "Hσ") as "[$ Hth]"; [done |].
    iMod "Hclose" as "_". iModIntro. simpl. iSplit; [done |]. by iApply "HΦ".
  Qed.

  (** A thread is started by who holds it: the new thread holds itself from then on, and must meet what a
      thread must (`wp_thread`); the starter learns it was started. *)
  Lemma wp_thread_start t u c E Φ :
    thread_is u c TNew -∗
    ▷ (thread_is u c TStarted -∗ WP (Running u (interp c VUnit) : thread) @ MaybeStuck; ⊤ {{ _, True }}) -∗
    ▷ (started u -∗ Φ (inr tt)) -∗
    wpp t (Vis (ThreadStart u) Ret) E Φ.
  Proof.
    iIntros "Hth Hfork HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iDestruct (interp_thread with "Hσ Hth") as %(i & Hu).
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop).
    simpl in Hop. rewrite Hu in Hop. destruct Hop as [-> ->].
    iMod (interp_thread_start _ u c i with "Hσ Hth") as "($ & Hth & #Hstarted)"; [done |].
    iMod "Hclose" as "_". iModIntro. simpl. rewrite Hu. simpl.
    iSplitL "Hfork Hth"; [iSplit; [by iApply "Hfork" | done] | by iApply "HΦ"].
  Qed.

  (** `join` returns when the thread is not running: of one that was started, when it has ended. *)
  Lemma wp_thread_join t u E Φ :
    started u -∗ ▷ ((ended u -∗ Φ (inr tt)) ∧ Φ (inl InterruptedException)) -∗
    wpp t (Vis (ThreadJoin u) Ret) E Φ.
  Proof.
    iIntros "#Hs HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iDestruct (interp_started with "Hσ Hs") as %Hb.
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop). iMod "Hclose" as "_". iModIntro.
    destruct Hop as [(-> & -> & Hnot) | (-> & _ & ->)]; simpl.
    - iAssert (ended u) as "#He".
      { iApply (interp_ended with "Hσ"). unfold over, begun in *.
        by destruct (s_th σ u) as [[c [] i] |]. }
      iFrame "Hσ". iSplit; [done |]. iDestruct "HΦ" as "[HΦ _]". by iApply "HΦ".
    - iSplitL "Hσ"; [by iApply interp_clear |]. iSplit; [done |]. by iDestruct "HΦ" as "[_ $]".
  Qed.

  Lemma wp_thread_join_any t u E Φ :
    ▷ (Φ (inr tt) ∧ Φ (inl InterruptedException)) ⊢ wpp t (Vis (ThreadJoin u) Ret) E Φ.
  Proof.
    iIntros "HΦ". iApply wpP_op. iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose !>" (x σ' Hop). iMod "Hclose" as "_". iModIntro.
    destruct Hop as [(-> & -> & Hnot) | (-> & _ & ->)]; simpl.
    - iFrame "Hσ". iSplit; [done |]. by iDestruct "HΦ" as "[$ _]".
    - iSplitL "Hσ"; [by iApply interp_clear |]. iSplit; [done |]. by iDestruct "HΦ" as "[_ $]".
  Qed.

  (** A thread: it holds itself, runs its program, and at its end gives itself up; that it has ended is then
      a fact. *)
  Lemma wp_thread t c (p : prog mres) (Ψ : final → iProp Σ) :
    wpp t p ⊤ (λ r, thread_is t c TStarted ∗ (ended t ={⊤}=∗ Ψ (t, r)))
    ⊢ WP (Running t p : thread) @ MaybeStuck; ⊤ {{ Ψ }}.
  Proof.
    iIntros "H". rewrite -{2}(pbind_ret p). iApply "H". iIntros (r) "[Hth HΨ]".
    iApply wp_lift_step; [done |]. iIntros (σ ns κs nt) "Hσ".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hclose".
    iSplit; [done |]. iIntros "!>" (e2 σ2 efs κ κs' -> [_ (-> & -> & ->)]) "_".
    iMod (interp_thread_exit with "Hσ Hth") as "[$ #He]". iMod "Hclose" as "_".
    iMod ("HΨ" with "He") as "HΨ". iModIntro. simpl. iSplit; [| done].
    by iApply (wp_value _ _ _ (Ended t r) (t, r)).
  Qed.

End rules.
