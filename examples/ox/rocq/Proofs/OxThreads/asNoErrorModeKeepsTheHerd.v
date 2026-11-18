Require Export FrFlowGen.OxThreads.asNoErrorModeKeepsTheHerd.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Whether a value is a Scala object the code names is decided: the comparison gives a truth value. *)
Lemma compared_with_an_object (a : val) (m : string) :
  equal Code_table a (VObj (Module m)) = oret true \/ equal Code_table a (VObj (Module m)) = oret false.
Proof.
  destruct a; try (right; reflexivity).
  match goal with o : obj |- _ => destruct o end; try (right; reflexivity).
  cbn. destruct (String.eqb _ _); [left | right]; reflexivity.
Qed.

(** Proven of `OxError.asNoErrorMode`'s tree. It reads the scope's error mode and compares it with the object
    that is no error mode. If they are the same it returns the scope itself. If not it reads the scope's vals
    and makes a scope of them, with no error mode, by the `apply` the compiler wrote: a scope that holds the
    herd it was made with, which is the herd read. *)
Lemma asNoErrorModeKeepsTheHerd_Proofs_complete : asNoErrorModeKeepsTheHerd_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade Hconstructed Hfields Hholds s from other to
    [(wm & m0 & b0 & ins0 & hs0 & Hm0 & Hmk) [c Hdone]].
  destruct (made_named C Hmk) as [r Hs].
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside Hcall] [sp Hend]]].
  { exfalso. exact (method_not_atomic C (Member "ox.Ox" "asNoErrorMode" ":ox.OxError") Hat Hs eq_refl). }
  assert (forall k, direct c from (history k) ->
    forall sp, history k = Event_Respond c from (Response_Returned other) sp ->
    scopeMade history other /\ heldIn L.OxError_herd other = heldIn L.OxError_herd s) as Hall.
  { refine (method_meets _ C (Member "ox.Ox" "asNoErrorMode" ":ox.OxError") Hcall Hs eq_refl _).
    intros args k Hargs _. apply vals_none in Hargs as ->.
    (* the error mode is read, and compared *)
    step. intros wem vem yem Hwem _ Hyem Htyem Hreadem. split; [miss |].
    meets_head.
    all: first
      [ match goal with |- context [equal Code_table ?a ?b] =>
          change b with (VObj (Module "ox.NoErrorMode") : val);
          destruct (compared_with_an_object a "ox.NoErrorMode") as [E | E]; rewrite E; clear E end
      | match goal with |- context [if ?b then _ else _] => destruct b end ].
    all: meets_head.
    (* the same: the scope itself is returned *)
    1, 3: apply meets_ret; intros rr Hk _ Hrr Hgives sp' Hresp; rewrite Hrr in Hresp; injection Hresp as -> _;
      pose proof (one_name N _ _ _ Hgives Hs) as ->;
      (split; [exists wm, m0, b0, ins0, hs0; split; [exact Hm0 | exact Hmk] | reflexivity]).
    (* not the same: the scope's herd is read, the herd it holds; then its other vals *)
    all: step_rule; intros wherd vherd yherd Hwherd _ Hyherd Htyherd Hreadherd; (split; [miss |]);
      apply (proj1 (proj1 (proj1 (proj1 (proj1 (Hfields s)))))) in Hreadherd; subst yherd.
    all: do 4 pass.
    (* a scope is made of them: it holds the herd read, and is an object of the class *)
    all: step; intros wmk ysmk Hwmk _ Hysmk Hinvmk; cbn in Hysmk;
      inversion Hysmk as [| ya ? yas ? Hya Hyas]; subst; pose proof (one_name N _ _ _ Hya Hyherd) as ->;
      inversion Hyas as [| yb ? ybs ? _ Hybs]; subst; inversion Hybs as [| yc ? ycs ? _ Hycs]; subst;
      inversion Hycs as [| yd ? yds ? _ Hyds]; subst; inversion Hyds as [| ye ? yes ? _ Hyes]; subst;
      apply args_one in Hyes as (yf & -> & _); (split; [miss |]);
      intros wmkd rmk spmk xmk Hwmkd Hrespmk Hgivesmk.
    all: meets_head.
    all: apply meets_ret; intros rr Hk _ Hrr Hgives sp' Hresp; rewrite Hrr in Hresp; injection Hresp as -> _.
    all: try (destruct Hgives; fail).
    all: destruct rmk as [ymk | ymk]; [| contradiction]; pose proof (one_name N _ _ _ Hgivesmk Hgives) as ->.
    all: assert (exists who, completedBy history (Invocation_mk
        L.OxError_apply_6
        [heldIn L.OxError_herd s; yb; yc; yd; ye; yf]) who wmk (Response_Returned other) (wmkd + 1)) as Hdonemk
      by (exists c; right; (split; [exists (Some from); exact Hinvmk |]); exists spmk;
        replace (wmkd + 1 - 1) with wmkd by lia; exact Hrespmk).
    all: split;
      [ apply (Hmade other (wmkd + 1)); exact (Hconstructed _ _ _ _ _ _ other wmk _ (wmkd + 1) Hdonemk eq_refl)
      | exact (Hholds _ _ _ _ _ _ other wmk _ (wmkd + 1) Hdonemk eq_refl) ]. }
  exact (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
