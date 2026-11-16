Require Export FrFlowGen.OxThreads.Whole.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia Classical PropExtensionality.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic FrFlow.Code.Witness.

(** An execution of the code in which things happen: one thread (reference 0) makes a herd (2) with a factory (1),
    and closes it. The herd's constructor (the call made at the moment 0) writes its four fields: the factory,
    the thread that makes it, a flag (3) and a set (4). Closing (14) checks the thread is the owner (15), sets
    the flag, makes its two variables (5, 6), finds the set empty, reads that no interruption was kept, and
    returns. Each call is shown to follow the code read from Ox, event by event. *)
Lemma made_and_closed_runs :
  Code_runs (history_of
    [ Event_Invoke (Value_Reference 0) None (Invocation_mk
        "ox.internal.ThreadHerd <init> java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd"
        [Value_Reference 1]);
      Event_Make (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd"
        [Held_mk "ox.internal.ThreadHerd threadFactory" Value_Null;
         Held_mk "ox.internal.ThreadHerd herdOwner" Value_Null;
         Held_mk "ox.internal.ThreadHerd shutdownInProgress" Value_Null;
         Held_mk "ox.internal.ThreadHerd threads" Value_Null];
      Event_Mark (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd threadFactory";
      Event_Write (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd threadFactory"
        (Value_Reference 1);
      Event_Atomic (Value_Reference 0) (Some 0)
        (Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" [])
        (Response_Returned (Value_Reference 0)) [];
      Event_Mark (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd herdOwner";
      Event_Write (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd herdOwner"
        (Value_Reference 0);
      Event_Atomic (Value_Reference 0) (Some 0) (Invocation_mk
        "java.util.concurrent.atomic.AtomicBoolean <init> scala.Boolean:java.util.concurrent.atomic.AtomicBoolean"
        [Value_Bool_ (false = true)]) (Response_Returned (Value_Reference 3)) [];
      Event_Mark (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd shutdownInProgress";
      Event_Write (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd shutdownInProgress"
        (Value_Reference 3);
      Event_Atomic (Value_Reference 0) (Some 0) (Invocation_mk
        "java.util.concurrent.ConcurrentHashMap$ newKeySet 1:java.util.concurrent.ConcurrentHashMap$.KeySetView"
        []) (Response_Returned (Value_Reference 4)) [];
      Event_Mark (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd threads";
      Event_Write (Value_Reference 0) (Some 0) (Value_Reference 2) "ox.internal.ThreadHerd threads"
        (Value_Reference 4);
      Event_Respond (Value_Reference 0) 0 (Response_Returned (Value_Reference 2)) [];
      Event_Invoke (Value_Reference 0) None (Invocation_mk
        "ox.internal.ThreadHerd interruptAllAndJoinUntilCompleted :scala.Unit" [Value_Reference 2]);
      Event_Invoke (Value_Reference 0) (Some 14) (Invocation_mk
        "ox.internal.ThreadHerd assertOnOwnerThread :scala.Unit" [Value_Reference 2]);
      Event_Atomic (Value_Reference 0) (Some 15)
        (Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" [])
        (Response_Returned (Value_Reference 0)) [];
      Event_Read (Value_Reference 0) (Some 15) (Value_Reference 2) "ox.internal.ThreadHerd herdOwner"
        (Value_Reference 0);
      Event_Respond (Value_Reference 0) 15 (Response_Returned Value_Unit_) [];
      Event_Read (Value_Reference 0) (Some 14) (Value_Reference 2) "ox.internal.ThreadHerd shutdownInProgress"
        (Value_Reference 3);
      Event_Atomic (Value_Reference 0) (Some 14) (Invocation_mk
        "java.util.concurrent.atomic.AtomicBoolean set scala.Boolean:scala.Unit"
        [Value_Reference 3; Value_Bool_ (true = true)]) (Response_Returned Value_Unit_) [];
      Event_Make (Value_Reference 0) (Some 14) (Value_Reference 5) "<var>:scala.collection.immutable.Set"
        [Held_mk "value" (Value_Reference 7)];
      Event_Make (Value_Reference 0) (Some 14) (Value_Reference 6) "<var>:java.lang.InterruptedException"
        [Held_mk "value" Value_Null];
      Event_Read (Value_Reference 0) (Some 14) (Value_Reference 2) "ox.internal.ThreadHerd threads"
        (Value_Reference 4);
      Event_Atomic (Value_Reference 0) (Some 14) (Invocation_mk
        "java.util.concurrent.ConcurrentHashMap$.CollectionView isEmpty :scala.Boolean" [Value_Reference 4])
        (Response_Returned (Value_Bool_ (true = true))) [];
      Event_Read (Value_Reference 0) (Some 14) (Value_Reference 6) "value" Value_Null;
      Event_Respond (Value_Reference 0) 14 (Response_Returned Value_Unit_) [] ]).
Proof.
  match goal with |- Code_runs (history_of ?l) => set (events := l) end.
  pose (N := naming_of
    [(0, VTid 0%nat); (1, vext "java.util.concurrent.ThreadFactory" 0); (2, vref "ox.internal.ThreadHerd" 0);
     (3, vext "java.util.concurrent.atomic.AtomicBoolean" 1);
     (4, vext "java.util.concurrent.ConcurrentHashMap$KeySetView" 2);
     (5, vref "<var>:scala.collection.immutable.Set" 1); (6, vref "<var>:java.lang.InterruptedException" 2);
     (7, vdata "scala.collection.immutable.Set" [VList []])]
    (fun r : nat => match r with
      | 0%nat => "ox.internal.ThreadHerd"%string
      | 1%nat => "<var>:scala.collection.immutable.Set"%string
      | _ => "<var>:java.lang.InterruptedException"%string
      end) eq_refl eq_refl).
  assert (Hmade : goes Code_table Code_classes N (history_of events) (Value_Reference 0) 0 1
    (Running (constructs Code_table "ox.internal.ThreadHerd" [vext "java.util.concurrent.ThreadFactory" 0]))).
  { own_at 1. own_at 2. own_at 3. own_at 4. own_at 5. own_at 6. own_at 7. own_at 8. own_at 9. own_at 10.
    own_at 11. own_at 12. own_at 13. rests. }
  assert (Howned : goes Code_table Code_classes N (history_of events) (Value_Reference 0) 15 16
    (Running (run Code_table (Method (Member "ox.internal.ThreadHerd" "assertOnOwnerThread" ":scala.Unit"))
      (VList [vref "ox.internal.ThreadHerd" 0])))).
  { own_at 16. own_at 17. own_at 18. rests. }
  assert (Hclosed : goes Code_table Code_classes N (history_of events) (Value_Reference 0) 14 15
    (Running (run Code_table
      (Method (Member "ox.internal.ThreadHerd" "interruptAllAndJoinUntilCompleted" ":scala.Unit"))
      (VList [vref "ox.internal.ThreadHerd" 0])))).
  { own_at 15. answer_at 18. own_at 19. own_at 20. own_at 21. own_at 22. own_at 23. own_at 24. own_at 25.
    own_at 26. rests. }
  exists N. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - intros i a inside s cls r d y ys H Hy Himpl. scan H; injection H as <- <- Hm <- <-.
    + lazy in Hy. discriminate Hy.
    + lazy in Hy. injection Hy as <- <-.
      pose proof (impl_labelled _ _ _ _ Himpl) as Hin. rewrite <- Hm in Hin. vm_compute in Hin.
      destruct Hin as [<- | []]. vm_compute in Himpl. injection Himpl as <-.
      exists []. split; [apply Forall2_nil | split; [apply Forall2_nil |]]. follows_by Hclosed.
    + lazy in Hy. injection Hy as <- <-.
      pose proof (impl_labelled _ _ _ _ Himpl) as Hin. rewrite <- Hm in Hin. vm_compute in Hin.
      destruct Hin as [<- | []]. vm_compute in Himpl. injection Himpl as <-.
      exists []. split; [apply Forall2_nil | split; [apply Forall2_nil |]]. follows_by Howned.
  - intros i a inside owner name signature c0 d ys H Hc Hmod Himpl.
    pose proof (module_labelled _ _ _ _ _ _ Hc Hmod Himpl) as Hin.
    scan H; injection H as <- <- Hm <-; rewrite <- Hm in Hin; vm_compute in Hin; destruct Hin.
  - intros i a inside m f y ys H Happ Hy Hwritten.
    scan H; injection H as <- <- <- Hys; try discriminate Hys; vm_compute in Happ; discriminate Happ.
  - intros w a inside m ys resp spawns H. scan H; injection H as <- <- <- <- <- <-; (split; [| split]).
    all: try (intros s cls r d y ys' Hm Hys Hy Himpl;
      first [ discriminate Hys | injection Hys as <- <-; lazy in Hy; discriminate Hy
            | injection Hys as <- <-; pose proof (plain_not_referred _ _ Hy) as Hr; discriminate Hr ]).
    all: try (intros owner name signature c0 d Hm Hc Hmod Himpl;
      pose proof (module_labelled _ _ _ _ _ _ Hc Hmod Himpl) as Hin; rewrite <- Hm in Hin; vm_compute in Hin;
      destruct Hin).
    all: intros f y ys' Happ Hys Hy Hwritten; vm_compute in Happ; discriminate Happ.
  - split.
    + intros w b inside y cls hs H. scan H; injection H as <- <- <- <- <-; eexists; unfold names; reflexivity.
    + intros w w' b inside y cls hs b' inside' cls' hs' H H'.
      scan H; injection H as <- <- <- <- <-; scan H'; first [reflexivity | discriminate H'].
  - split.
    + intros k k' a called r r' spawns spawns' H H'.
      scan H; injection H as <- <- <- <-; scan H'; first [reflexivity | discriminate H'].
    + intros k a called r spawns H. scan H; injection H as <- <- <- <-; lia.
  - split.
    + intros i a inside cls c0 signature ys H Hc Hmod.
      pose proof (constructor_labelled _ _ signature _ Hc) as Hin.
      scan H; injection H as <- <- Hm <-; rewrite <- Hm in Hin; vm_compute in Hin;
        [destruct Hin as [<- | []] | destruct Hin | destruct Hin].
      vm_compute in Hc. injection Hc as <-.
      exists [vext "java.util.concurrent.ThreadFactory" 0]. split; [fact | split; [fact |]]. follows_by Hmade.
    + intros w a inside cls c0 signature ys resp spawns H Hc Hmod.
      pose proof (constructor_labelled _ _ signature _ Hc) as Hin.
      scan H; injection H as <- <- Hm <- <- <-; rewrite <- Hm in Hin; vm_compute in Hin; destruct Hin.
  - intros w a inside yo f y cls r H Hyo Hvar Hmk Hwrites.
    scan H; injection H as <- <- <- <- <-; lazy in Hyo; injection Hyo as <- <-; try discriminate Hvar.
    right. split.
    + intros k b ins y' Hk Hw. scan Hw; discriminate Hw.
    + exists 22, (Value_Reference 0), (Some 14), "<var>:java.lang.InterruptedException"%string. reflexivity.
Qed.

(** What the model states at the bottom can hold together: the execution above, in which a herd is made and
    closed, meets each. A field of the herd holds what its constructor wrote there; the set never has an
    element; the flag is set from the moment closing sets it. Of what the model assumes of forks, of threads
    started and of scopes, this execution says nothing: it has none. *)
Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  pose proof made_and_closed_runs as Hruns.
  match type of Hruns with Code_runs (history_of ?l) => set (events := l) in Hruns end.
  pose (held := fun (f : string) (h : Value) =>
    match h with
    | Value_Reference 2 =>
        if String.eqb f "ox.internal.ThreadHerd threadFactory" then Value_Reference 1
        else if String.eqb f "ox.internal.ThreadHerd herdOwner" then Value_Reference 0
        else if String.eqb f "ox.internal.ThreadHerd shutdownInProgress" then Value_Reference 3
        else if String.eqb f "ox.internal.ThreadHerd threads" then Value_Reference 4
        else Value_Null
    | _ => Value_Null
    end).
  pose (flag := fun (s : Value) (w : Z) => s = Value_Reference 3 /\ 20 < w).
  exists (history_of events), (fun _ _ _ => False), held, flag.
  split; [exact Hruns |]. clear Hruns.
  split.
  { intros s x who from [H _]. absent H. }
  split.
  { intros s b who from [H _]. absent H. }
  split.
  { intros s who from [H _]. absent H. }
  split.
  { intros s rest _ from response to [who H] _. reveal H. f_equal. apply truth_is. tauto. }
  split.
  { intros s f c from [[H _] _]. absent H. }
  split.
  { intros s f c x from m [H _]. absent H. }
  split.
  { intros s x w [_ H]. destruct H. }
  split.
  { intros made by_ w Hw H. reveal H; lia. }
  split.
  { intros f r t c a b i from [[[who H] _] _]. absent H. }
  split.
  { intros h f x c k [_ H]. absent H. }
  split.
  { intros h f x c k g t a [[_ H] _]. absent H. }
  split.
  { intros t who from [H _]. absent H. }
  split.
  { intros x y who from [H _]. absent H. }
  split.
  { intros f r t a b s [[who H] _]. absent H. }
  split.
  { intros h t code made m [[_ H] _]. absent H. }
  split.
  { intros h c i H. reveal H.
    - intros w [[Hw Hover] _]. destruct (Z_le_gt_dec w 26) as [Hle | Hgt].
      + exists 26. split; [exact Hle | right; eexists; eexists; reflexivity].
      + exfalso. apply Hover. exists 26. eexists. eexists. split; [lia | reflexivity].
    - intros w [[Hw Hover] _]. destruct (Z_le_gt_dec w 18) as [Hle | Hgt].
      + exists 18. split; [exact Hle | right; eexists; eexists; reflexivity].
      + exfalso. apply Hover. exists 18. eexists. eexists. split; [lia | reflexivity]. }
  split.
  { intros h r code _ who from [H _]. absent H. }
  split.
  { intros who from [H _]. absent H. }
  split.
  { intros s x who from [H _]. absent H. }
  split.
  { intros x who from [H _]. absent H. }
  split.
  { intros c s from to (supervisor & errorMode & parent & locals & code & ended & a & b & [[H _] _]). absent H. }
  split.
  { intros c s from to (supervisor & errorMode & parent & locals & code & ended & a & b & [[H _] _]). absent H. }
  split.
  { intros s from response to [who H]. absent H. }
  split.
  { intros s. split; intros from response to [who H]; absent H. }
  split.
  { intros h finalizers supervisor errorMode parent locals s from response to [who H]. absent H. }
  split.
  { intros h code t m w [[who H] _]. absent H. }
  split.
  { intros h g r q t i j [[[_ H] _] _]. absent H. }
  split.
  { intros s from response to [who H] _. reveal H. exists 24. split; [lia | intros y Hy; exact Hy]. }
  split.
  { intros h a b _ H. absent H. }
  split.
  { intros s from response to [who H]. reveal H. left. f_equal. apply truth_is. tauto. }
  split.
  { intros s f c _ from response to H. absent H. }
  split.
  { intros h who from made by_ w [[[H _] Hmade] Htouch]. reveal H. reveal Hmade; reveal Htouch. reflexivity. }
  split.
  { intros h from made by_ inside w [[H Hmade] Hwrites]. reveal H. reveal Hmade; reveal Hwrites. }
  split.
  { intros t from response to [who H]. absent H. }
  split.
  { intros x _ from response to [who H]. absent H. }
  split.
  { intros t from response to [who H]. absent H. }
  split.
  { intros h code c w H. absent H. }
  split.
  { intros s v w [[_ Hne] Heq]. destruct (classic (s = Value_Reference 3 /\ w = 20)) as [[-> ->] | Hno].
    - left. exists (Value_Reference 0). right. exists (Response_Returned Value_Unit_), (Some 14), [].
      rewrite <- Heq. replace (flag (Value_Reference 3) (20 + 1)) with (true = true); [reflexivity |].
      apply propositional_extensionality. unfold flag.
      split; [intros _; split; [reflexivity | lia] | reflexivity].
    - exfalso. apply Hne. rewrite <- Heq. apply propositional_extensionality. unfold flag.
      split; intros [Hs Hw]; (split; [exact Hs |]); [lia |].
      destruct (Z.eq_dec w 20) as [Ew | Nw]; [destruct (Hno (conj Hs Ew)) | lia]. }
  split.
  { intros h w (x & by_ & from & to & Hto & Hctor) method rest by2 w1 Hcall. reveal Hctor.
    change (held "ox.internal.ThreadHerd shutdownInProgress"%string (Value_Reference 2))
      with (Value_Reference 3) in *.
    reveal Hcall. exists 14. split; [right; eexists; eexists; reflexivity |].
    somewhere ltac:(eexists; reflexivity). }
  split.
  { intros b x from to [who Hmade] method w Hon. reveal Hmade. reveal Hon. somewhere ltac:(reflexivity). }
  split.
  { intros h w (x & by_ & from & to & Hto & Hctor) method rest by2 w1 Hcall. reveal Hctor.
    change (held "ox.internal.ThreadHerd threads"%string (Value_Reference 2)) with (Value_Reference 4) in *.
    reveal Hcall. exists 14. split; [right; eexists; eexists; reflexivity |].
    somewhere ltac:(eexists; reflexivity). }
  split.
  { intros s from to [who Hmade] method w Hon. reveal Hmade. reveal Hon. somewhere ltac:(reflexivity). }
  split.
  { intros s b from response to [who H]. absent H. }
  split.
  { intros s b from value to [who H]. reveal H. exists 20. split; [lia |].
    apply propositional_extensionality. unfold flag.
    split; [reflexivity | intros _; split; [reflexivity | lia]]. }
  split.
  { intros s b from response to [who H]. reveal H. reflexivity. }
  split.
  { intros h code c t from b m other [[H _] _]. absent H. }
  split.
  { intros f r h1 x. split; intros who from w [[_ H] _]; absent H. }
  split.
  { intros b s t. repeat (intros; split). all: intros who from w [[_ H] _]; absent H. }
  split.
  { intros t s x. repeat (intros; split). all: intros who from w [[_ H] _]; absent H. }
  split.
  { intros s. repeat (intros; split). all: intros who from w [[_ H] _]; absent H. }
  split.
  { intros t outer from inside w [[[Hlt Hbegun] Hover] Hdoes]. reveal Hbegun; unfold does in Hdoes; scan_at w.
    all: try lia; try (destruct Hdoes as [_ <-]); try destruct Hdoes; try (left; reflexivity).
    all: first
      [ exfalso; apply Hover; exists 13; eexists; eexists; split; [lia | reflexivity]
      | exfalso; apply Hover; exists 18; eexists; eexists; split; [lia | reflexivity]
      | exfalso; apply Hover; exists 26; eexists; eexists; split; [lia | reflexivity]
      | right; exists (Invocation_mk "ox.internal.ThreadHerd assertOnOwnerThread :scala.Unit" [Value_Reference 2]),
          15; split; [split; [lia | reflexivity] |];
        intros (k & a & sp & Hk & Hr); scan Hr; lia ]. }
  split.
  { intros h w H. reveal H.
    all: exists (Value_Reference 1), (Value_Reference 0), 0, 14;
      split; [lia | right; split; [exists None; reflexivity | exists []; reflexivity]]. }
  split.
  { intros h. repeat split; intros w by_ inside written Hw; scan Hw; inversion Hw; subst; reflexivity. }
  split.
  { intros h. repeat split; intros w by_ inside found Hw; scan Hw; inversion Hw; subst; reflexivity. }
  split.
  { intros c from response to H. reveal H; reflexivity. }
  split.
  { intros s x from value to [who H]. absent H. }
  intros s x w [[_ H] _]. destruct H.
Qed.
