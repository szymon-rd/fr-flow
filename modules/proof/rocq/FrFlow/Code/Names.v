(** The references of an execution written out as it is produced.

    A run names its values as it goes: a value that is the same in every execution is itself (`plain_of`), any
    other is given the next reference the first time an event speaks of it (`extend`), and `name_of` is how an
    event writes a value. Here is what makes the table a naming (`naming_of`): it stays one as it grows, what an
    event wrote stays the name of the value, and each value an event speaks of has a name. *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Code.Walk FrFlow.Code.Witness.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** How an event writes a value: itself where it is the same in every execution, else its reference. *)
Definition name_of (refs : list (Z * val)) (v : val) : Value :=
  match plain_of v with
  | Some x => x
  | None =>
      match find (fun kv => val_eqb (snd kv) v) refs with
      | Some kv => Value_Reference (fst kv)
      | None => Value_Str "UNNAMED"
      end
  end.

(** The references known, with one more for each of the values given that has none yet. *)
Fixpoint extend (refs : list (Z * val)) (vs : list val) : list (Z * val) :=
  match vs with
  | [] => refs
  | v :: rest =>
      extend (if (referred v && negb (existsb (fun kv => val_eqb (snd kv) v) refs))%bool
              then (refs ++ [(Z.of_nat (List.length refs), v)])%list else refs) rest
  end.

(** ** A table that is a naming *)

(** The references are the places in the table, from `k`. *)
Definition keyed_from (k : Z) (refs : list (Z * val)) : Prop :=
  forall i kv, nth_error refs i = Some kv -> fst kv = k + Z.of_nat i.

(** The table as a run builds it: each reference is its place, no value is there twice, and each is a value a
    reference can be. *)
Definition good (refs : list (Z * val)) : Prop :=
  keyed_from 0 refs /\ NoDup (map snd refs) /\ Forall (fun kv => referred (snd kv) = true) refs.

Lemma keyed_tail (k : Z) (kv : Z * val) (rest : list (Z * val)) :
  keyed_from k (kv :: rest) -> fst kv = k /\ keyed_from (k + 1) rest.
Proof.
  intros H. split; [rewrite (H 0%nat kv eq_refl); lia |].
  intros i kv' Hi. rewrite (H (S i) kv' Hi). lia.
Qed.

Lemma keyed_above (k : Z) (refs : list (Z * val)) (kv : Z * val) : keyed_from k refs -> In kv refs -> k <= fst kv.
Proof. intros H Hin. apply In_nth_error in Hin as [i Hi]. rewrite (H i kv Hi). lia. Qed.

Lemma good_from_named (k : Z) (refs : list (Z * val)) :
  keyed_from k refs -> NoDup (map snd refs) -> Forall (fun kv => referred (snd kv) = true) refs ->
  well_named refs = true.
Proof.
  revert k. induction refs as [| [n v] rest IH]; intros k Hk Hd Hr; cbn; [reflexivity |].
  destruct (keyed_tail k (n, v) rest Hk) as [Hn Hrest]. cbn in Hn. subst n.
  inversion Hd as [| ? ? Hnot Hd']; subst. inversion Hr as [| ? ? Hv Hr']; subst. cbn in Hv.
  rewrite Hv, (IH (k + 1) Hrest Hd' Hr'). cbn. rewrite andb_true_r.
  apply forallb_forall. intros [m u] Hin. cbn.
  pose proof (keyed_above (k + 1) rest (m, u) Hrest Hin) as Hm. cbn in Hm.
  rewrite (proj2 (Z.eqb_neq m k)) by lia. cbn.
  destruct (val_eqb u v) eqn:E; [| reflexivity].
  apply val_eqb_eq in E. subst u. exfalso. apply Hnot. apply in_map_iff. exists (m, v). auto.
Qed.

Lemma good_named (refs : list (Z * val)) : good refs -> well_named refs = true.
Proof. intros (Hk & Hd & Hr). exact (good_from_named 0 refs Hk Hd Hr). Qed.

Lemma good_nil : good [].
Proof.
  split; [intros i kv H; destruct i; discriminate H | split; [constructor | constructor]].
Qed.

(** ** A table that grows *)

Lemma extend_more (refs : list (Z * val)) (vs : list val) : exists more, extend refs vs = (refs ++ more)%list.
Proof.
  revert refs. induction vs as [| v rest IH]; intros refs; cbn; [exists []; rewrite app_nil_r; reflexivity |].
  destruct (referred v && negb (existsb (fun kv => val_eqb (snd kv) v) refs))%bool.
  - destruct (IH (refs ++ [(Z.of_nat (List.length refs), v)])%list) as [more E].
    exists ((Z.of_nat (List.length refs), v) :: more). rewrite E, <- app_assoc. reflexivity.
  - apply IH.
Qed.

Lemma good_one (refs : list (Z * val)) (v : val) :
  good refs -> referred v = true -> ~ In v (map snd refs) ->
  good (refs ++ [(Z.of_nat (List.length refs), v)])%list.
Proof.
  intros (Hk & Hd & Hr) Hv Hnot. split; [| split].
  - intros i kv Hi. destruct (Nat.lt_ge_cases i (List.length refs)) as [Hlt | Hge].
    + rewrite nth_error_app1 in Hi by exact Hlt. exact (Hk i kv Hi).
    + rewrite nth_error_app2 in Hi by exact Hge.
      destruct (i - List.length refs)%nat as [| j] eqn:E; cbn in Hi; [| destruct j; discriminate Hi].
      injection Hi as <-. cbn. f_equal. lia.
  - rewrite map_app. cbn. apply NoDup_app; [exact Hd | repeat constructor; intros [] | ].
    intros x Hx [<- | []]. exact (Hnot Hx).
  - apply Forall_app. split; [exact Hr | repeat constructor; exact Hv].
Qed.

Lemma good_extend (refs : list (Z * val)) (vs : list val) : good refs -> good (extend refs vs).
Proof.
  revert refs. induction vs as [| v rest IH]; intros refs Hg; cbn; [exact Hg |].
  destruct (referred v) eqn:Hv; cbn; [| apply IH, Hg].
  destruct (existsb (fun kv => val_eqb (snd kv) v) refs) eqn:E; cbn; [apply IH, Hg |].
  apply IH, good_one; [exact Hg | exact Hv |].
  intros Hin. apply in_map_iff in Hin as (kv & <- & Hkv).
  assert (existsb (fun kv0 => val_eqb (snd kv0) (snd kv)) refs = true) as X.
  { apply existsb_exists. exists kv. split; [exact Hkv | apply val_eqb_eq; reflexivity]. }
  rewrite X in E. discriminate E.
Qed.

(** Each value given has a name in the table extended: itself, or a reference. *)
Definition has_name (refs : list (Z * val)) (v : val) : Prop := referred v = false \/ In v (map snd refs).

Lemma has_name_more (refs more : list (Z * val)) (v : val) : has_name refs v -> has_name (refs ++ more) v.
Proof. intros [H | H]; [left; exact H | right; rewrite map_app; apply in_or_app; left; exact H]. Qed.

Lemma extend_names (refs : list (Z * val)) (vs : list val) (v : val) : In v vs -> has_name (extend refs vs) v.
Proof.
  revert refs. induction vs as [| u rest IH]; intros refs Hin; [destruct Hin |]. cbn.
  destruct Hin as [-> | Hin]; [| apply IH, Hin].
  destruct (referred v) eqn:Hv; [| left; exact Hv]. cbn.
  match goal with |- has_name (extend ?r rest) v => destruct (extend_more r rest) as [more ->] end.
  apply has_name_more. right.
  destruct (existsb (fun kv => val_eqb (snd kv) v) refs) eqn:E; cbn.
  - apply existsb_exists in E as (kv & Hkv & Ekv). apply val_eqb_eq in Ekv. subst v.
    apply in_map. exact Hkv.
  - rewrite map_app. apply in_or_app. right. left. reflexivity.
Qed.

Lemma extend_keeps (refs : list (Z * val)) (vs : list val) (v : val) :
  has_name refs v -> has_name (extend refs vs) v.
Proof. intros H. destruct (extend_more refs vs) as [more ->]. apply has_name_more, H. Qed.

(** ** What an event wrote stays the name *)

Lemma find_first {A : Type} (f : A -> bool) (xs more : list A) (x : A) :
  find f xs = Some x -> find f (xs ++ more) = Some x.
Proof.
  induction xs as [| y rest IH]; cbn; [discriminate |]. destruct (f y); [auto | exact IH].
Qed.

Lemma name_of_more (refs more : list (Z * val)) (v : val) :
  has_name refs v -> name_of (refs ++ more) v = name_of refs v.
Proof.
  intros H. unfold name_of. destruct (plain_of v) eqn:P; [reflexivity |].
  destruct H as [H | H]; [unfold referred in H; rewrite P in H; discriminate H |].
  apply in_map_iff in H as (kv & <- & Hkv).
  destruct (find (fun kv0 => val_eqb (snd kv0) (snd kv)) refs) as [found |] eqn:F.
  - rewrite (find_first _ refs more found F). reflexivity.
  - exfalso. pose proof (find_none _ _ F kv Hkv) as X. cbn in X.
    rewrite (proj2 (val_eqb_eq (snd kv) (snd kv)) eq_refl) in X. discriminate X.
Qed.

(** ** The name names the value *)

Lemma in_ref_at (refs : list (Z * val)) (n : Z) (v : val) :
  well_named refs = true -> In (n, v) refs -> ref_at refs n = Some v.
Proof.
  induction refs as [| [m u] rest IH]; cbn; [intros _ [] |]. intros Hw Hin.
  apply andb_true_iff in Hw as [Hw Hrest]. apply andb_true_iff in Hw as [_ Hfresh].
  destruct Hin as [E | Hin].
  - injection E as -> ->. rewrite Z.eqb_refl. reflexivity.
  - pose proof (proj1 (forallb_forall _ _) Hfresh _ Hin) as X. cbn in X.
    apply andb_true_iff in X as [X _]. apply negb_true_iff in X.
    rewrite Z.eqb_sym, X. exact (IH Hrest Hin).
Qed.

Lemma name_of_names (refs : list (Z * val)) (places : nat -> string)
    (Hw : well_named refs = true) (Hp : placed places refs = true) (v : val) :
  has_name refs v -> names (naming_of refs places Hw Hp) (name_of refs v) v.
Proof.
  intros H. unfold names, name_of. cbn [val_of naming_of].
  destruct (plain_of v) as [x |] eqn:P.
  - pose proof (plain_of_val v x P) as Hx.
    destruct x; try exact Hx. destruct v as [| | | e | o | |]; cbn in P; try discriminate P.
    + destruct (exn_class e); discriminate P.
    + destruct o; discriminate P.
  - destruct H as [H | H]; [unfold referred in H; rewrite P in H; discriminate H |].
    apply in_map_iff in H as (kv & <- & Hkv).
    destruct (find (fun kv0 => val_eqb (snd kv0) (snd kv)) refs) as [found |] eqn:F.
    + apply find_some in F as [Hfound Efound]. apply val_eqb_eq in Efound.
      cbn. apply in_ref_at; [exact Hw |]. rewrite <- Efound. destruct found. exact Hfound.
    + exfalso. pose proof (find_none _ _ F kv Hkv) as X. cbn in X.
      rewrite (proj2 (val_eqb_eq (snd kv) (snd kv)) eq_refl) in X. discriminate X.
Qed.
