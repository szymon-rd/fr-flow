(** The other steps of a program, as `Places.v` has a scope opened: a fork made, a fork past its body, a scope
    ended and left, a fork that acts. Each from the place of the thread that takes it. *)

From Stdlib Require Import ZArith List Lia Sorted.
From stdpp Require Import gmap.
From FrFlow.Jvm Require Import Machine.
From FrFlow.Scala Require Import Tree Value.
Require Import FrFlowGen.OxScopes.Domain Proofs.OxScopes.Lemmas.
From Ox.Proof Require Export Places.

Lemma hasOpen_same (s s' : Scopes) w h : scope_of s' = scope_of s -> hasOpen s' w h <-> hasOpen s w h.
Proof. intros E. unfold hasOpen. rewrite E. reflexivity. Qed.

Lemma openedAt_same (s s' : Scopes) h : scope_of s' = scope_of s -> openedAt s' h = openedAt s h.
Proof. intros E. unfold openedAt. rewrite E. reflexivity. Qed.

Lemma stack_same (s s' : Scopes) w stack : scope_of s' = scope_of s -> stack_ok s w stack -> stack_ok s' w stack.
Proof.
  intros E [Ho Hs]. split.
  - intros h. rewrite (hasOpen_same s s' _ _ E). apply Ho.
  - apply (sorted_same s); [| exact Hs]. intros a _. apply openedAt_same, E.
Qed.

(** ** A fork made

    By a thread that has the scope open or is a fork of it, of a thread that has no place yet. The scope's set
    holds the new thread from then on. *)

Lemma agrees_forks taken places herds w r stack q c :
  agrees taken places herds -> places !! w = Some (r, stack) -> (r = ForkIn q \/ In q stack) ->
  places !! c = None ->
  let e := Step_Forks (zt w) (zs q) (zt c) in
  agrees (taken ++ e :: nil) (<[c := (ForkIn q, nil)]> places) herds /\
  (forall q' held held', set_ok taken q' held -> (forall x, In x held -> In x held') ->
     (q' = q -> In (VTid c : val) held') -> set_ok (taken ++ e :: nil) q' held').
Proof.
  intros Ha Hw Hin Hc e.
  destruct Ha as [Hv Hrole Hstack Hknown Hherds]. set (s := ran none taken) in *.
  pose proof (Hrole w r stack Hw) as Hrw. destruct (Hstack w r stack Hw) as [Hopen Hsorted].
  assert (forall k, (fork_of s k <> None \/ exists h x, scope_of s h = Some x /\ owner_of x = k) -> k <> zt c)
    as Hother.
  { intros k Hk ->. destruct (Hknown (zt c) Hk) as (c' & Ec & Hsome).
    apply Nat2Z.inj in Ec as <-. rewrite Hc in Hsome. by destruct Hsome. }
  assert (isNew s (zt c)) as Hnew.
  { split.
    - destruct (@fork_of Scopes Scopes_has_fork s (zt c)) eqn:E; [| done].
      apply (Hother (zt c)); [left; by rewrite E | done].
    - intros h x Hx Ho. apply (Hother (zt c)); [right; by exists h, x | done]. }
  assert (canTake s e) as Hcan.
  { unfold e, canTake. split; [| exact Hnew]. destruct Hin as [-> | Hin].
    - right. unfold role_ok in Hrw. eexists. split; [exact Hrw | done].
    - left. apply Hopen. by exists q. }
  set (s' := afterStep s e). assert (ran none (taken ++ e :: nil) = s') as Eran by apply ran_snoc.
  assert (scope_of s' = scope_of s) as Escope by apply forks_scope.
  assert (forall k, fork_of s' (zt k) =
      if PeanoNat.Nat.eq_dec k c then Some (Fork_mk (zs q) Life_Running) else fork_of s (zt k)) as Efork.
  { intros k. unfold s', e. rewrite forks_fork. destruct (PeanoNat.Nat.eq_dec k c) as [-> | Hne].
    - by rewrite ite_true.
    - rewrite ite_false; [done |]. intros E. by apply Nat2Z.inj in E. }
  split; [split |]; unfold set_ok; rewrite ?Eran.
  - apply taken_snoc; [exact Hv | exact Hcan].
  - intros w' r' stack' Hw'. unfold role_ok. rewrite Efork. destruct (PeanoNat.Nat.eq_dec w' c) as [-> | Hne].
    + rewrite lookup_insert_eq in Hw'. assert (r' = ForkIn q) as -> by (by simplify_eq). done.
    + rewrite lookup_insert_ne in Hw' by done. exact (Hrole w' r' stack' Hw').
  - intros w' r' stack' Hw'. destruct (PeanoNat.Nat.eq_dec w' c) as [-> | Hne].
    + rewrite lookup_insert_eq in Hw'. assert (stack' = nil) as -> by (by simplify_eq). split; [| constructor].
      intros h. rewrite (hasOpen_same s s' _ _ Escope). split; [| intros (? & _ & [])].
      intros (x & Hx & Ho & _). exfalso. destruct Hnew as [_ Hnew]. exact (Hnew h x Hx Ho).
    + rewrite lookup_insert_ne in Hw' by done. apply (stack_same s); [exact Escope |].
      exact (Hstack w' r' stack' Hw').
  - intros k Hk. destruct (Z.eq_dec k (zt c)) as [-> | Hne].
    + exists c. split; [done |]. rewrite lookup_insert_eq. eauto.
    + destruct (Hknown k) as (w' & -> & Hsome).
      { destruct Hk as [Hf | (h & x & Hx & Ho)].
        - left. unfold s', e in Hf. rewrite forks_fork, ite_false in Hf by done. exact Hf.
        - right. exists h, x. by rewrite Escope in Hx. }
      exists w'. split; [done |]. rewrite lookup_insert_ne; [done |]. intros ->. done.
  - intros h Hh. apply Hherds. by rewrite Escope in Hh.
  - intros q' held held' Hset Hsub Hadd t (f & Hf & Hsc & Hrun). rewrite Efork in Hf.
    destruct (PeanoNat.Nat.eq_dec t c) as [-> | Hne].
    + apply Hadd. injection Hf as <-. cbn in Hsc. apply Nat2Z.inj in Hsc. by symmetry.
    + apply Hsub, Hset. by exists f.
Qed.

(** ** A fork past its body

    The thread has no scope open, and takes itself out of its scope's set. *)

Lemma agrees_finish taken places herds t q :
  agrees taken places herds -> places !! t = Some (ForkIn q, nil) ->
  let e := Step_Finish (zt t) in
  agrees (taken ++ e :: nil) (<[t := (Past, nil)]> places) herds /\
  (forall q' held held', set_ok taken q' held -> (forall x, In x held -> x <> VTid t -> In x held') ->
     set_ok (taken ++ e :: nil) q' held').
Proof.
  intros Ha Ht e.
  destruct Ha as [Hv Hrole Hstack Hknown Hherds]. set (s := ran none taken) in *.
  pose proof (Hrole t _ _ Ht) as Hrt. unfold role_ok in Hrt. destruct (Hstack t _ _ Ht) as [Hopen _].
  assert (canTake s e) as Hcan.
  { unfold e, canTake. split.
    - eexists. split; [exact Hrt | done].
    - intros h Hh. apply Hopen in Hh as (? & _ & []). }
  set (s' := afterStep s e). assert (ran none (taken ++ e :: nil) = s') as Eran by apply ran_snoc.
  assert (scope_of s' = scope_of s) as Escope by apply finish_scope.
  assert (forall k, fork_of s' (zt k) =
      if PeanoNat.Nat.eq_dec k t then Some (Fork_mk (zs q) Life_Finished) else fork_of s (zt k)) as Efork.
  { intros k. unfold s', e. rewrite (finish_fork s (zt t) _ (zt k) Hrt).
    destruct (PeanoNat.Nat.eq_dec k t) as [-> | Hne].
    - by rewrite ite_true.
    - rewrite ite_false; [done |]. intros E. by apply Nat2Z.inj in E. }
  split; [split |]; unfold set_ok; rewrite ?Eran.
  - apply taken_snoc; [exact Hv | exact Hcan].
  - intros w' r' stack' Hw'. unfold role_ok. rewrite Efork. destruct (PeanoNat.Nat.eq_dec w' t) as [-> | Hne].
    + rewrite lookup_insert_eq in Hw'. assert (r' = Past) as -> by (by simplify_eq). by eexists.
    + rewrite lookup_insert_ne in Hw' by done. exact (Hrole w' r' stack' Hw').
  - intros w' r' stack' Hw'. apply (stack_same s); [exact Escope |].
    destruct (PeanoNat.Nat.eq_dec w' t) as [-> | Hne].
    + rewrite lookup_insert_eq in Hw'. assert (stack' = nil) as -> by (by simplify_eq). exact (Hstack t _ _ Ht).
    + rewrite lookup_insert_ne in Hw' by done. exact (Hstack w' r' stack' Hw').
  - intros k Hk. destruct (Hknown k) as (w' & -> & Hsome).
    { destruct Hk as [Hf | (h & x & Hx & Ho)].
      - left. destruct (Z.eq_dec k (zt t)) as [-> | Hne]; [by rewrite Hrt |].
        unfold s', e in Hf. rewrite (finish_fork s (zt t) _ k Hrt), ite_false in Hf by done. exact Hf.
      - right. exists h, x. by rewrite Escope in Hx. }
    exists w'. split; [done |]. destruct (PeanoNat.Nat.eq_dec w' t) as [-> | Hne].
    + rewrite lookup_insert_eq. eauto.
    + by rewrite lookup_insert_ne.
  - intros h Hh. apply Hherds. by rewrite Escope in Hh.
  - intros q' held held' Hset Hsub u (f & Hf & Hsc & Hrun). rewrite Efork in Hf.
    destruct (PeanoNat.Nat.eq_dec u t) as [-> | Hne]; [injection Hf as <-; cbn in Hrun; discriminate |].
    apply Hsub; [apply Hset; by exists f |]. intros E. by simplify_eq.
Qed.

(** ** A scope ended and left

    By the thread that has it open innermost, when its set holds no thread: every fork of it is past its body. *)

Lemma agrees_end taken places herds w r stack q :
  agrees taken places herds -> places !! w = Some (r, q :: stack) -> set_ok taken q nil ->
  let e := Step_End (zt w) (zs q) in
  let l := Step_Leave (zt w) (zs q) in
  agrees (taken ++ e :: l :: nil) (<[w := (r, stack)]> places) herds /\
  (forall q' held, set_ok taken q' held -> set_ok (taken ++ e :: l :: nil) q' held).
Proof.
  intros Ha Hw Hempty e l.
  destruct Ha as [Hv Hrole Hstack Hknown Hherds]. set (s := ran none taken) in *.
  destruct (Hstack w r _ Hw) as [Hopen Hsorted].
  assert (hasOpen s (zt w) (zs q)) as (x & Hx & Hown & Hnot) by (apply Hopen; exists q; split; [done | by left]).
  apply StronglySorted_inv in Hsorted as [Hs Hall]. rewrite Forall_forall in Hall.
  assert (canTake s e) as Hcan.
  { unfold e, canTake. split; [split |].
    - by exists x.
    - intros other Ho. apply Hopen in Ho as (q1 & -> & [<- | Hin]); [lia |].
      specialize (Hall q1 Hin). unfold later_first in Hall. lia.
    - intros t f Hf Hsc. destruct f as [fs [|]]; [| done]. exfalso. cbn in Hsc. subst fs.
      destruct (Hknown t) as (u & -> & _); [left; by rewrite Hf |].
      apply (Hempty u). eexists. split; [exact Hf | done]. }
  set (s' := afterStep s e).
  assert (taken ++ e :: l :: nil = (taken ++ e :: nil) ++ l :: nil) as Etwo by (by rewrite <- app_assoc).
  assert (ran none (taken ++ e :: l :: nil) = s') as Eran by (by rewrite Etwo, !ran_snoc).
  assert (canTake s' l) as Hleave.
  { unfold l, canTake. exists (Scope_mk (Scope_owner x) (Scope_parent x) (Scope_opened x) True). split.
    - unfold s', e. rewrite (end_scope s _ _ x _ Hx). by rewrite ite_true.
    - split; [exact Hown | exact I]. }
  split; [split |]; unfold set_ok; rewrite ?Eran.
  - rewrite Etwo. apply taken_snoc; [apply taken_snoc; [exact Hv | exact Hcan] |]. rewrite ran_snoc. exact Hleave.
  - intros w' r' stack' Hw'. assert (role_ok s w' r') as H.
    { destruct (PeanoNat.Nat.eq_dec w' w) as [-> | Hne].
      + rewrite lookup_insert_eq in Hw'. assert (r' = r) as -> by (by simplify_eq). exact (Hrole w r _ Hw).
      + rewrite lookup_insert_ne in Hw' by done. exact (Hrole w' r' stack' Hw'). }
    unfold role_ok in *. unfold s', e. by rewrite end_fork.
  - intros w' r' stack' Hw'. destruct (PeanoNat.Nat.eq_dec w' w) as [-> | Hne].
    + rewrite lookup_insert_eq in Hw'. assert (stack' = stack) as -> by (by simplify_eq). split.
      * intros h. unfold s', e. rewrite (end_hasOpen s _ _ x _ _ Hx), Hopen. split.
        -- intros [(q1 & -> & [<- | Hin]) Hneq]; [done | by exists q1].
        -- intros (q1 & -> & Hin). split; [exists q1; split; [done | by right] |].
           intros E. apply Nat2Z.inj in E as ->. specialize (Hall q Hin). unfold later_first in Hall. lia.
      * apply (sorted_same s); [| exact Hs]. intros a _. unfold s', e. apply (end_openedAt s _ _ x _ Hx).
    + rewrite lookup_insert_ne in Hw' by done. destruct (Hstack w' r' stack' Hw') as [Ho Hs']. split.
      * intros h. unfold s', e. rewrite (end_hasOpen s _ _ x _ _ Hx), Ho. split; [by intros [H _] |].
        intros (q1 & -> & Hin). split; [by exists q1 |]. intros E. apply Nat2Z.inj in E as ->.
        destruct (proj2 (Ho (zs q))) as (y & Hy & Hoy & _); [by exists q |].
        rewrite Hx in Hy. injection Hy as <-. rewrite Hown in Hoy. by apply Nat2Z.inj in Hoy.
      * apply (sorted_same s); [| exact Hs']. intros a _. unfold s', e. apply (end_openedAt s _ _ x _ Hx).
  - intros k Hk. destruct (Hknown k) as (w' & -> & Hsome).
    { destruct Hk as [Hf | (h & y & Hy & Ho)].
      - left. unfold s', e in Hf. by rewrite end_fork in Hf.
      - unfold s', e in Hy. rewrite (end_scope s _ _ x _ Hx) in Hy. destruct (Z.eq_dec h (zs q)) as [-> | Hne].
        + rewrite ite_true in Hy by done. injection Hy as <-. right. exists (zs q), x. split; [exact Hx | exact Ho].
        + rewrite ite_false in Hy by done. right. by exists h, y. }
    exists w'. split; [done |]. destruct (PeanoNat.Nat.eq_dec w' w) as [-> | Hne].
    + rewrite lookup_insert_eq. eauto.
    + by rewrite lookup_insert_ne.
  - intros h Hh. apply Hherds. unfold s', e in Hh. rewrite (end_scope s _ _ x _ Hx) in Hh.
    destruct (Z.eq_dec h (zs q)) as [-> | Hne]; [by rewrite Hx | by rewrite ite_false in Hh].
  - intros q' held Hset t (f & Hf & Hrun). apply Hset. unfold s', e in Hf. rewrite end_fork in Hf. by exists f.
Qed.

(** ** A fork that acts: it can, while it is not past its body. *)

Lemma agrees_act taken places herds t q stack :
  agrees taken places herds -> places !! t = Some (ForkIn q, stack) ->
  forall before e after,
    tookBetween (taken ++ Step_Act (zt t) (zs q) :: nil) before e after -> canTake (ran none before) e.
Proof.
  intros Ha Ht. apply taken_snoc; [apply Ha |]. pose proof (a_role _ _ _ Ha t _ _ Ht) as Hr.
  eexists. split; [exact Hr | done].
Qed.
