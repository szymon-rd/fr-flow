(** A Scala `object` with state, initialised by the first thread that names it (`Meaning.module_init`), as a proof
    of a program that names it sees it.

    The object is in one of three states, kept in an invariant: not yet initialised; being initialised by a
    thread, which holds half of it and so alone writes its fields; initialised, its fields fixed for good and
    what is known of them (`P`) everyone's. The rules are the steps of `module_init` and of an initialiser:
    naming the object (`Enter`), writing a field of it while it is initialised, and the write that ends its
    initialisation.

    A thread that names the object while it is itself initialising it is told it is initialised (JLS 12.4.2).
    A proof of code outside the initialiser must know it is not that thread: it shows something only one
    holder per thread can have (`tok`), which the initialising thread leaves in the invariant until it is
    done. *)

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From FrFlow.Scala Require Export Logic.

Definition initN : namespace := nroot .@ "init".

(** The fields of an object that thread `t` is initialising. *)
Definition initialising (fields : list (string * val)) (t : tid) : Prop :=
  field fields init_field = None ∧ holder fields init_field = Some t.

Lemma initialising_enter (unset : list (string * val)) (t : tid) :
  field unset init_field = None → initialising (with_field unset (entered init_field) (VTid t)) t.
Proof.
  intros H. split; [by rewrite field_with_other | by rewrite /holder field_with_same].
Qed.

Lemma initialising_mark (fields : list (string * val)) (t : tid) (name : string) (v : val) :
  initialising fields t → writing name ≠ init_field → writing name ≠ entered init_field →
  initialising (with_field fields (writing name) v) t.
Proof. intros [Hf Hh] H1 H2. split; [by rewrite field_with_other | by rewrite /holder field_with_other]. Qed.

Lemma initialising_written (fields : list (string * val)) (t : tid) (name : string) (v : val) :
  initialising fields t → name ≠ init_field → name ≠ entered init_field →
  writing name ≠ init_field → writing name ≠ entered init_field →
  initialising (written fields name v) t.
Proof.
  intros [Hf Hh] H1 H2 H3 H4. rewrite /written. split.
  - by rewrite field_without_other; [rewrite field_with_other |].
  - by rewrite /holder field_without_other; [rewrite field_with_other |].
Qed.

Section kept.
  Context `{!jvmGS code obj Σ}.

  (** The object at `r`, of class `cls`, with the fields `unset` before it is initialised. *)
  Definition module_body (r : nat) (cls : string) (unset : list (string * val))
      (tok : tid → iProp Σ) (P : list (string * val) → iProp Σ) : iProp Σ :=
    r ↦obj (cls, unset)
    ∨ (∃ fields u, r ↦obj{#1/2} (cls, fields) ∗ ⌜initialising fields u⌝ ∗ tok u)
    ∨ (∃ fields, r ↦obj□ (cls, fields) ∗ ⌜field fields init_field = Some VUnit⌝ ∗ P fields).

  Definition module_inv (r : nat) (cls : string) (unset : list (string * val))
      (tok : tid → iProp Σ) (P : list (string * val) → iProp Σ) : iProp Σ :=
    inv (initN .@ r) (module_body r cls unset tok P).
End kept.

Section modules.
  Context `{!jvmGS code obj Σ}.
  Context (I : code → val → Machine.P code obj (Machine.res code obj)).
  Local Instance modules_irisGS : irisGS (jvm I) Σ := jvm_irisGS I.

  Context (r : nat) (cls : string) (unset : list (string * val)).
  Context (tok : tid → iProp Σ) (P : list (string * val) → iProp Σ).
  Context `{!∀ u, Timeless (tok u), !∀ f, Persistent (P f)}.
  Context (tok_once : ∀ u, tok u -∗ tok u -∗ False).
  Context (unset_init : field unset init_field = None) (unset_holder : holder unset init_field = None).

  Notation module_body := (module_body r cls unset tok P).
  Notation module_inv := (module_inv r cls unset tok P).

  (** The thread that holds half of the object is the one initialising it: with the other half it has it
      whole. *)
  Lemma module_mine E t fields :
    initialising fields t →
    ▷ module_body -∗ r ↦obj{#1/2} (cls, fields) ={E}=∗ r ↦obj (cls, fields) ∗ tok t.
  Proof.
    iIntros ([Hf Hh]) "H Hmine". iDestruct "H" as "[>Hr | [H | H]]".
    - iDestruct (obj_at_valid with "Hr Hmine") as %[Hv _]. exfalso.
      rewrite dfrac_op_own dfrac_valid_own in Hv. by apply Qp.not_add_le_l in Hv.
    - iDestruct "H" as (fields' u) "(>Hr & >[%Hf' %Hh'] & >Htok)".
      iDestruct (obj_at_valid with "Hr Hmine") as %[_ [= <-]]. assert (u = t) as -> by congruence.
      iModIntro. iFrame "Htok". iApply obj_at_halve. iFrame.
    - iDestruct "H" as (fields') "(>Hr & >%Hf' & _)".
      iDestruct (obj_at_valid with "Hr Hmine") as %[_ [= <-]]. congruence.
  Qed.

  (** ** The object named: it is initialised, or the thread is the one to initialise it *)

  Lemma wp_module_enter t E Φ :
    ↑initN.@r ⊆ E →
    module_inv -∗ tok t -∗
    ▷ ((∀ fields, r ↦obj□ (cls, fields) -∗ ⌜field fields init_field = Some VUnit⌝ -∗ P fields -∗ tok t -∗
          Φ (inr (Some VUnit))) ∧
       (r ↦obj{#1/2} (cls, with_field unset (entered init_field) (VTid t)) -∗ Φ (inr None))) -∗
    wpP I t (Vis (Enter r init_field OfClass) Ret) E Φ.
  Proof.
    iIntros (HE) "#Hinv Htok HΦ". iApply wp_enter. iInv "Hinv" as "H" "Hclose".
    iDestruct "H" as "[>Hr | [H | H]]".
    - iModIntro. iExists (DfracOwn 1), cls, unset. iFrame "Hr". rewrite unset_init unset_holder /=.
      iIntros "!>". iSplit; [done |]. iIntros "Hr". iDestruct (obj_at_halve with "Hr") as "[Hr1 Hr2]".
      iMod ("Hclose" with "[Hr1 Htok]") as "_".
      { iNext. iRight. iLeft. iExists _, t. iFrame "Hr1 Htok". iPureIntro. by apply initialising_enter. }
      iModIntro. iDestruct "HΦ" as "[_ HΦ]". by iApply "HΦ".
    - iDestruct "H" as (fields u) "(>Hr & >[%Hf %Hh] & >Htok')".
      destruct (decide (u = t)) as [-> | Hne]; [iDestruct (tok_once with "Htok Htok'") as %[] |].
      iModIntro. iExists (DfracOwn (1/2)), cls, fields. iFrame "Hr". rewrite Hf Hh /=.
      iIntros "!> Hr". iMod ("Hclose" with "[Hr Htok']") as "_".
      { iNext. iRight. iLeft. iExists fields, u. by iFrame. }
      iModIntro. by iIntros (?).
    - iDestruct "H" as (fields) "(>#Hr & >%Hf & #HP)".
      iModIntro. iExists DfracDiscarded, cls, fields. iFrame "Hr". rewrite Hf /=.
      iIntros "!> _". iMod ("Hclose" with "[]") as "_".
      { iNext. iRight. iRight. iExists fields. by iFrame "Hr HP". }
      iModIntro. iDestruct "HΦ" as "[HΦ _]". by iApply ("HΦ" with "Hr [//] HP Htok").
  Qed.

  (** ** A field of the object written by the thread that initialises it: marked, then stored *)

  Lemma wp_module_mark t name fields E Φ :
    ↑initN.@r ⊆ E → initialising fields t → writer fields name = None →
    writing name ≠ init_field → writing name ≠ entered init_field →
    module_inv -∗ r ↦obj{#1/2} (cls, fields) -∗
    ▷ (r ↦obj{#1/2} (cls, with_field fields (writing name) (VTid t)) -∗ Φ (inr tt)) -∗
    wpP I t (Vis (ObjMark r name) Ret) E Φ.
  Proof.
    iIntros (HE Hi Hw Hn1 Hn2) "#Hinv Hmine HΦ". iApply wp_obj_mark. iInv "Hinv" as "H" "Hclose".
    iMod (module_mine with "H Hmine") as "[Hr Htok]"; [done |].
    iModIntro. iExists cls, fields. iFrame "Hr". iSplit; [done |]. iIntros "!> Hr".
    iDestruct (obj_at_halve with "Hr") as "[Hr1 Hr2]". iMod ("Hclose" with "[Hr1 Htok]") as "_".
    { iNext. iRight. iLeft. iExists _, t. iFrame "Hr1 Htok". iPureIntro. by apply initialising_mark. }
    iModIntro. by iApply "HΦ".
  Qed.

  Lemma wp_module_store t name v fields E Φ :
    ↑initN.@r ⊆ E → initialising fields t → writer fields name = Some t →
    name ≠ init_field → name ≠ entered init_field →
    writing name ≠ init_field → writing name ≠ entered init_field →
    module_inv -∗ r ↦obj{#1/2} (cls, fields) -∗
    ▷ (r ↦obj{#1/2} (cls, written fields name v) -∗ Φ (inr tt)) -∗
    wpP I t (Vis (ObjSet r name v) Ret) E Φ.
  Proof.
    iIntros (HE Hi Hw Hn1 Hn2 Hn3 Hn4) "#Hinv Hmine HΦ". iApply wp_obj_set. iInv "Hinv" as "H" "Hclose".
    iMod (module_mine with "H Hmine") as "[Hr Htok]"; [done |].
    iModIntro. iExists cls, fields. iFrame "Hr". iSplit; [by rewrite Hw |]. iIntros "!> Hr".
    iDestruct (obj_at_halve with "Hr") as "[Hr1 Hr2]". iMod ("Hclose" with "[Hr1 Htok]") as "_".
    { iNext. iRight. iLeft. iExists _, t. iFrame "Hr1 Htok". iPureIntro. by apply initialising_written. }
    iModIntro. by iApply "HΦ".
  Qed.

  (** ** The write that ends the initialisation: the object's fields are fixed, and known to all *)

  Lemma wp_module_done t fields E Φ :
    ↑initN.@r ⊆ E → initialising fields t → writer fields init_field = None →
    module_inv -∗ r ↦obj{#1/2} (cls, fields) -∗ P (written fields init_field VUnit) -∗
    ▷ (tok t -∗ r ↦obj□ (cls, written fields init_field VUnit) -∗ Φ (inr tt)) -∗
    wpP I t (Vis (ObjSet r init_field VUnit) Ret) E Φ.
  Proof.
    iIntros (HE Hi Hw) "#Hinv Hmine #HP HΦ". iApply wp_obj_set. iInv "Hinv" as "H" "Hclose".
    iMod (module_mine with "H Hmine") as "[Hr Htok]"; [done |].
    iModIntro. iExists cls, fields. iFrame "Hr". iSplit; [by rewrite Hw |]. iIntros "!> Hr".
    iMod (obj_at_persist with "Hr") as "#Hr".
    iMod ("Hclose" with "[]") as "_".
    { iNext. iRight. iRight. iExists _. iFrame "Hr HP". iPureIntro.
      rewrite /written field_without_other; [apply field_with_same | done]. }
    iModIntro. iApply ("HΦ" with "Htok Hr").
  Qed.

End modules.

(** ** Naming an object, in a walk

    An object with no state is its name; one with state that runs nothing when it is made is its place: the
    walk computes those. Naming one that is initialised on first use is a program of its own
    (`Meaning.module_init`): a walk stops at it, and a proof about that object's class goes on from there (by
    the rules above). *)
Global Opaque module_init.
