Require Export FrFlowGen.OxThreads.aConstructedScopesValsAreWritten.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic.

(** Proven of what making a scope runs, gone through to its end: the call of the constructor makes the object
    itself, and writes each field it marks before it marks the next; what it returns at the end is that object.
    And a scope's vals are marked and written only inside the call that makes it. *)
Lemma aConstructedScopesValsAreWritten_Proofs_complete : aConstructedScopesValsAreWritten_Obl_complete.
Proof.
  intros history [N C] Hassigned s w (x & x1 & x2 & x3 & x4 & x5 & c & from & to & Hto & Hdone)
    field by_ inside later [Hfield Hlater].
  revert by_ inside later Hlater.
  destruct Hdone as [[(ins & sp & Hat) _] | [[inside0 Hbegun] [sp Hend]]].
  { destruct (constructor_not_atomic C "ox.OxError"
      "2,ox.internal.ThreadHerd,java.util.concurrent.atomic.AtomicReference,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError"
      Hat ltac:(vm_compute; reflexivity) eq_refl). }
  assert (forall k, direct c from (history k) ->
    forall sp, history k = Event_Respond c from (Response_Returned s) sp ->
    (exists m hs, history m = Event_Make c (Some from) s "ox.OxError" hs) /\
    forall m f, m < k -> history m = Event_Mark c (Some from) s f ->
      exists k' v, m < k' /\ k' < k /\ history k' = Event_Write c (Some from) s f v) as Hall.
  { refine (constructor_meets _ C "ox.OxError"
      "2,ox.internal.ThreadHerd,java.util.concurrent.atomic.AtomicReference,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError"
      Hbegun ltac:(vm_compute; reflexivity) eq_refl _).
    intros args k Hargs Hpassed.
    repeat (match goal with H : Forall2 _ _ _ |- _ => inversion H; subst; clear H end).
    (* the object is made *)
    step. intros wherd xherd Hwherd _ Hopherd. cbn [op_event] in Hopherd.
    destruct Hopherd as (rherd & yherd & hsherd & -> & Hclassherd & Hyherd & Hholdingherd & Heherd).
    split; [miss |].
    (* each field is marked and then written what the call was given *)
    repeat pass.
    (* and what the call returns is the object *)
    meets_head. apply meets_ret. intros rr Hk Hpast Hrr Hgives sp' Hresp.
    rewrite Hrr in Hresp. injection Hresp as -> _.
    pose proof (one_name N _ _ _ Hyherd Hgives) as ->.
    rename s into yherd.
    unfold at_place in *. rewrite <- Hclassherd in Hyherd.
    repeat match goal with Hp : names N ?yo (vref (class_at N rherd) rherd) |- _ =>
      tryif constr_eq yo yherd then fail else (pose proof (one_name N _ _ _ Hp Hyherd); subst yo; clear Hp) end.
    split; [exists wherd, hsherd; exact Heherd |].
    intros m f Hm HM. pose proof (Hpast m Hm ltac:(rewrite HM; cbn; auto)) as Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]); [.. | destruct Hin].
    all: first [ solve [miss_now] |
      match goal with E : ?hist ?x = Event_Mark _ _ _ _ |- _ =>
        tryif constr_eq E HM then fail else (rewrite E in HM; injection HM as Ef; subst f) end;
      match goal with W : ?hist ?k' = Event_Write _ _ _ _ ?v |- _ =>
        exists k', v; split; [lia | split; [lia | exact W]] end ]. }
  destruct (Hall (to - 1) ltac:(rewrite Hend; cbn; auto) sp Hend) as [Hmade Hmarks].
  intros by_ inside later Hlater. assert (to - 1 < later) as Hlt by lia.
  exact (made_then_settled history N s "ox.OxError" c from (to - 1) _ sp field C Hmade Hend
    (fun x Hx => constructor_over C "ox.OxError"
      "2,ox.internal.ThreadHerd,java.util.concurrent.atomic.AtomicReference,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError"
      Hbegun ltac:(vm_compute; reflexivity) eq_refl Hend Hx)
    Hmarks (fun b i x Ha => Hassigned s field b i x (conj Hfield Ha)) by_ inside later Hlt).
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
