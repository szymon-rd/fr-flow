Require Export FrFlowGen.OxThreads.whatUnsupervisedRunsEndsOnceItsCodeDoes.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.

(** Proven of `unsupervised`'s tree, and of the tree of the function it writes. Where the call hands a function
    to `scopedWithCapability`, that function is one written there: applied to the scope, given its turn, it
    applies the code to the scope, which is responded to, and returns what that gave. *)
Lemma whatUnsupervisedRunsEndsOnceItsCodeDoes_Proofs_complete : whatUnsupervisedRunsEndsOnceItsCodeDoes_Obl_complete.
Proof.
  intros history [N C] Hproceeds locals code c from s g k m [[[[Hcalled Hmakes] Hcode] Hfm] Happ].
  pose proof (Hproceeds locals code c from s g k m (conj (conj Hcalled Hmakes) Happ)) as Hmoves.
  apply proceeds_moves in Hmoves.
  destruct Hcalled as [[inside Hcall] | (a0 & ins & sp & Hat)].
  2: { exfalso. exact (module_not_atomic C "ox.unsupervised$package$" "unsupervised"
      "1,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hat ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)). }
  destruct Hmakes as [Hinvk | (rk & spk & Hatk)].
  2: { exfalso. exact (module_not_atomic C "ox.unsupervised$package$" "scopedWithCapability"
      "1,ox.Ox,scala.Function1:java.lang.Object" Hatk ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)). }
  assert (forall w, direct c from (history w) ->
    forall s g, history w = Event_Invoke c (Some from) (Invocation_mk
      L.unsupervised_scopedWithCapability [s; g]) ->
    forall m, from < m -> calledBy history (Invocation_mk L.Function_apply [g; s]) c m ->
    moves history c m -> codeEndsIn history code s c from ->
    begun history (Invocation_mk L.Function_apply [g; s]) c m /\ exists to, overBy history c m to) as Hall.
  { refine (module_meets _ C "ox.unsupervised$package$" "unsupervised"
      "1,ox.ForkLocalMap,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl eq_refl
      ltac:(vm_compute; reflexivity) _).
    intros args w Hargs Hpassed.
    inversion Hargs as [| ? vlocals ? rest Hvlocals Hrest]; subst.
    apply vals_one in Hrest as (vcode & -> & Hvcode).
    inversion Hpassed as [| p1 v1 ps1 vs1 Hlocals Hpassed1]; subst.
    inversion Hpassed1 as [| p2 v2 ps2 vs2 Hcodetyped _]; subst. typed Hlocals. typed Hcodetyped.
    (* the thread's scope is read, and a scope is made: neither is the event asked of *)
    step. intros wget ysget Hwget _ Hysget Hmkget. split; [miss |].
    intros wgetd rget xget Hwgetd Hdoneget Hgivesget Hretget.
    meets_head.
    { apply meets_ret. intros rr Hk Hpast Hrr Hgives s0 g0 E. rewrite Hrr in E. discriminate E. }
    step_rule. intros wapp ysapp Hwapp _ Hysapp Hinvapp. split; [miss |].
    intros wappd rapp spapp xapp Hwappd Hrespapp Hgivesapp.
    meets_head.
    all: try (apply meets_ret; intros rr Hk Hpast Hrr Hgives s0 g0 E; rewrite Hrr in E; discriminate E).
    (* running a function in the scope is called: the function is the one written here *)
    step_rule. intros wsc yssc Hwsc _ Hyssc Hinvsc. cbn in Hyssc.
    apply args_two in Hyssc as (ysc & yg & -> & Hysc & Hyg).
    split.
    { intros s0 g0 E m0 Hfm0 Happ0 Hmoves0 Hcode0. rewrite Hinvsc in E. injection E as <- <-.
      lazymatch type of Hyg with names _ _ (VCode ?fn) =>
        assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
      destruct Happ0 as [[inside0 Happ0] | (a1 & inside1 & sp1 & Hat1)];
        [| exfalso; exact (function_not_atomic C Hat1 eq_refl Hyg Hwritten)].
      split; [exists inside0; exact Happ0 |].
      refine (function_leads _ C Happ0 eq_refl Hyg Hwritten Hmoves0 _).
      intros args' Hargs' Hgiven. apply vals_one in Hargs' as (vs0 & -> & Hvs0).
      cbv beta iota delta [given] in Hgiven. inversion Hgiven as [| pg vg psg vsg Hscopetyped _]; subst.
      typed Hscopetyped.
      (* it applies the code to the scope: that is responded to; and it returns what that gave *)
      lstep. intros wcode mcode ycode yscode Hwcode Hqcode Hmcode Hycode Hyscode Hinvcode.
      cbv [called_as] in Hmcode. subst mcode. cbn in Hyscode. apply args_one in Hyscode as (ys1 & -> & Hys1).
      pose proof (one_name N _ _ _ Hys1 Hvs0) as ->. pose proof (one_name N _ _ _ Hycode Hvcode) as ->.
      split.
      { destruct (Hcode0 wcode) as [_ (to & Hover)].
        { split; [lia | left; exists (Some m0); exact Hinvcode]. }
        exact (over_responded _ _ m0 _ _ Hover). }
      intros wcoded rcode spcode xcode Hwcoded Hqcoded Hrespcode Hgivescode.
      leads_head.
      all: apply leads_ret; intros wr rr Hwr Hqr Hrr Hgives; exists (wr + 1), wr, rr, []; (split; [lia | exact Hrr]). }
    intros wscd rsc spsc xsc Hwscd Hrespsc Hgivessc.
    meets_head.
    all: apply meets_ret; intros rr Hk Hpast Hrr Hgives s0 g0 E; rewrite Hrr in E; discriminate E. }
  exact (Hall k ltac:(rewrite Hinvk; cbn; auto) s g Hinvk m Hfm Happ Hmoves Hcode).
Qed.

(** Its part can hold: an execution in which nothing happens meets it. *)
