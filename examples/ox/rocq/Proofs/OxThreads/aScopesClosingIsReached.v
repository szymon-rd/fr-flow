Require Export FrFlowGen.OxThreads.aScopesClosingIsReached.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.

(** Proven of `scopedWithCapability`'s tree, and of the tree of the function it applies. Given its turn, the call
    reads the thread's scope and sets it, each responded to, and applies a function of its own. That function,
    given its turn, applies the code to the scope, which is responded to; whatever that gave, it asks the scope
    for its herd, which is responded to with the herd the scope holds; and it calls closing on that herd. *)
Lemma aScopesClosingIsReached_Proofs_complete : aScopesClosingIsReached_Obl_complete.
Proof.
  intros heldIn history [N C] Hproceeds Happproceeds Hscoperesp Hherdresp Hherd Hscope s g c from [Hcalled Hcode].
  destruct Hcalled as [[inside Hcall] | (a0 & ins & sp & Hat)].
  2: { exfalso. exact (module_not_atomic C "ox.unsupervised$package$" "scopedWithCapability"
      "1,ox.Ox,scala.Function1:java.lang.Object" Hat ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)). }
  pose proof (proceeds_moves _ _ _ (Hproceeds s g c from (or_introl (ex_intro _ inside Hcall)))) as Hmoves.
  refine (module_leads _ C "ox.unsupervised$package$" "scopedWithCapability"
    "1,ox.Ox,scala.Function1:java.lang.Object" Hcall ltac:(vm_compute; reflexivity) eq_refl eq_refl
    ltac:(vm_compute; reflexivity) Hmoves _).
  intros args Hargs Hpassed.
  inversion Hargs as [| ? vscope ? rest Hvscope Hrest]; subst.
  apply vals_one in Hrest as (vcode & -> & Hvcode).
  inversion Hpassed as [| p1 v1 ps1 vs1 Hscopetyped Hpassed1]; subst.
  inversion Hpassed1 as [| p2 v2 ps2 vs2 Hcodetyped _]; subst. typed Hscopetyped. typed Hcodetyped.
  (* the thread's scope is read: that is responded to, and returns *)
  lstep. intros wget ysget Hwget Hqget Hysget Hmkget. apply args_none in Hysget as ->.
  split.
  { intros Hinv. destruct (proj1 (Hscoperesp s) c wget (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wgetd rget xget Hwgetd Hqgetd Hdoneget Hgivesget Hretget.
  destruct (proj1 (Hscope s) _ _ _ (done_by_someone Hdoneget)) as (yprevious & ->).
  destruct xget as [e | vprevious]; [contradiction |].
  (* and set to the scope: the same *)
  lstep. intros wset ysset Hwset Hqset Hysset Hmkset. cbn in Hysset. apply args_one in Hysset as (yset & -> & Hyset).
  pose proof (one_name N _ _ _ Hyset Hvscope) as ->.
  split.
  { intros Hinv. destruct (proj2 (Hscoperesp s) c wset (conj (ex_intro _ _ Hinv) I)) as (to & Hover).
    exact (over_responded _ _ from _ _ Hover). }
  intros wsetd rset xset Hwsetd Hqsetd Hdoneset Hgivesset Hretset.
  rewrite (proj2 (Hscope s) _ _ _ (done_by_someone Hdoneset)) in Hgivesset.
  destruct xset as [e | u]; [contradiction |].
  (* its own function is applied: closing is called in it *)
  lstep_done. intros wapp m yg ysg Hwapp Hqapp Hm Hyg Hysg Hinv. cbv [called_as] in Hm. subst m.
  cbn in Hysg. apply args_none in Hysg as ->.
  lazymatch type of Hyg with names _ _ (VCode ?fn) =>
    assert (written Code_files fn) as Hwritten by (apply written_function; vm_compute; reflexivity) end.
  pose proof (proceeds_moves _ _ _ (Happproceeds s g c from yg wapp
    (conj (or_introl (ex_intro _ inside Hcall)) (or_introl Hinv)))) as Hmoves2.
  refine (function_leads _ C Hinv eq_refl Hyg Hwritten Hmoves2 _).
  intros args' Hargs' _. apply vals_none in Hargs' as ->.
  (* the code is applied to the scope: that is responded to *)
  lstep. intros wcode mcode ycode yscode Hwcode Hqcode Hmcode Hycode Hyscode Hinvcode.
  cbv [called_as] in Hmcode. subst mcode.
  cbn in Hyscode. apply args_one in Hyscode as (yscope & -> & Hyscope).
  pose proof (one_name N _ _ _ Hyscope Hvscope) as ->. pose proof (one_name N _ _ _ Hycode Hvcode) as ->.
  split.
  { destruct (Hcode wcode) as [_ (to & Hover)].
    { split; [lia | left; exists (Some wapp); exact Hinvcode]. }
    exact (over_responded _ _ wapp _ _ Hover). }
  intros wcoded rcode spcode xcode Hwcoded Hqcoded Hrespcode Hgivescode.
  (* whatever it gave, the scope is asked for its herd: that is responded to, with the herd it holds *)
  leads_head.
  all: lstep_rule; intros wherd ysherd Hwherd Hqherd Hysherd Hmkherd; cbn in Hysherd;
    apply args_one in Hysherd as (yherdscope & -> & Hyherdscope);
    pose proof (one_name N _ _ _ Hyherdscope Hvscope) as ->;
    (split; [intros Hinvherd; destruct (Hherdresp s c wherd (conj (ex_intro _ _ Hinvherd) I)) as (to & Hover);
      exact (over_responded _ _ wapp _ _ Hover) |]);
    intros wherdd rherd xherd Hwherdd Hqherdd Hdoneherd Hgivesherd Hretherd;
    rewrite (Hherd s _ _ _ (done_by_someone Hdoneherd)) in Hgivesherd;
    (destruct xherd as [e' | vherd]; [contradiction |]).
  (* and closing is called on it *)
  all: lstep_done; intros wclose ysclose Hwclose Hqclose Hysclose Hinvclose;
    (lazymatch type of Hysclose with Forall2 _ _ (receiver ?v ++ _) =>
       match goal with Hrecv : receiver v = _ |- _ => rewrite Hrecv in Hysclose end end);
    cbn [app] in Hysclose; apply args_one in Hysclose as (yclose & -> & Hyclose);
    pose proof (one_name N _ _ _ Hyclose Hgivesherd) as ->;
    exists wclose; (split; [lia | left; exists (Some wapp); exact Hinvclose]).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
