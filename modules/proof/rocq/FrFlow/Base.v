(** FrFlow's support for the Rocq it generates: what the generated definitions are written with, and the tactics
    the generated theorems call. Fixed text of FrFlow's, on the standard library alone. *)
From Stdlib Require Export ZArith List String Lia Classical ClassicalDescription PropExtensionality
  FunctionalExtensionality Setoid Morphisms.
Export ListNotations.
#[global] Open Scope Z_scope.

(** A model's Booleans are propositions, and its `if` is on one: decided classically. *)
Definition ite {A : Type} (P : Prop) (a b : A) : A := if excluded_middle_informative P then a else b.
Definition decide (P : Prop) : Prop := P.

Lemma ite_true {A : Type} (P : Prop) (a b : A) : P -> ite P a b = a.
Proof. intro H. unfold ite. destruct (excluded_middle_informative P); [reflexivity | contradiction]. Qed.
Lemma ite_false {A : Type} (P : Prop) (a b : A) : ~ P -> ite P a b = b.
Proof. intro H. unfold ite. destruct (excluded_middle_informative P); [contradiction | reflexivity]. Qed.

(** Lists, with the inputs in the order the generated terms give them. *)
Definition List_filter {A : Type} (p : A -> Prop) (xs : list A) : list A :=
  filter (fun x => if excluded_middle_informative (p x) then true else false) xs.
Definition List_find {A : Type} (p : A -> Prop) (xs : list A) : option A :=
  find (fun x => if excluded_middle_informative (p x) then true else false) xs.
Definition List_foldl {A B : Type} (f : B -> A -> B) (init : B) (xs : list A) : B := fold_left f xs init.
Definition List_map {A B : Type} (f : A -> B) (xs : list A) : list B := map f xs.
Definition List_flatMap {A B : Type} (f : A -> list B) (xs : list A) : list B := flat_map f xs.
Definition List_zip {A B : Type} (xs : list A) (ys : list B) : list (A * B) := combine xs ys.
Definition List_Nodup {A : Type} (xs : list A) : Prop := NoDup xs.
Definition List_Pairwise {A : Type} (p : A -> A -> Prop) (xs : list A) : Prop := ForallOrdPairs p xs.
Definition Option_getD {A : Type} (o : option A) (d : A) : A := match o with Some a => a | None => d end.

Lemma List_filter_app {A : Type} (p : A -> Prop) (xs ys : list A) :
  List_filter p (xs ++ ys) = List_filter p xs ++ List_filter p ys.
Proof. apply filter_app. Qed.
Lemma List_filter_cons {A : Type} (p : A -> Prop) (x : A) (xs : list A) :
  List_filter p (x :: xs) = ite (p x) (x :: List_filter p xs) (List_filter p xs).
Proof. unfold List_filter, ite. simpl. destruct (excluded_middle_informative (p x)); reflexivity. Qed.
Lemma List_filter_nil {A : Type} (p : A -> Prop) : List_filter p (@nil A) = nil.
Proof. reflexivity. Qed.
Lemma List_filter_In {A : Type} (p : A -> Prop) (x : A) (xs : list A) :
  In x (List_filter p xs) <-> In x xs /\ p x.
Proof.
  unfold List_filter. rewrite filter_In. destruct (excluded_middle_informative (p x)); intuition discriminate.
Qed.
Lemma List_foldl_app {A B : Type} (f : B -> A -> B) (init : B) (xs ys : list A) :
  List_foldl f init (xs ++ ys) = List_foldl f (List_foldl f init xs) ys.
Proof. apply fold_left_app. Qed.
Lemma List_foldl_cons {A B : Type} (f : B -> A -> B) (init : B) (x : A) (xs : list A) :
  List_foldl f init (x :: xs) = List_foldl f (f init x) xs.
Proof. reflexivity. Qed.
Lemma List_foldl_nil {A B : Type} (f : B -> A -> B) (init : B) : List_foldl f init nil = init.
Proof. reflexivity. Qed.

Create Rewrite HintDb frflow.
#[global] Hint Rewrite @List_filter_app @List_filter_cons @List_filter_nil @List_foldl_app @List_foldl_cons
  @List_foldl_nil @List_filter_In @in_app_iff @app_nil_r @app_nil_l : frflow.

(** The definitions FrFlow generates: `frflow_auto` unfolds them. *)
Create HintDb frflow_defs.
#[global] Hint Unfold decide List_map List_flatMap List_zip List_Nodup Option_getD : frflow_defs.

(** The library's functions are rewritten by their lemmas, never computed by `cbn`. *)
Arguments ite : simpl never.
Arguments List_filter : simpl never.
Arguments List_find : simpl never.
Arguments List_foldl : simpl never.

(** Each `if` of the goal and the hypotheses, by cases of its condition. *)
Ltac frflow_case P :=
  let h := fresh "h" in
  destruct (classic P) as [h | h];
  [ repeat (rewrite (ite_true P) in * by exact h) | repeat (rewrite (ite_false P) in * by exact h) ].
Ltac frflow_split := repeat match goal with
  | |- context [ite ?P _ _] => frflow_case P
  | H : context [ite ?P _ _] |- _ => frflow_case P
  end.

(** Two propositions stated equal are each the other's condition: what the rewrites and the search read. *)
Lemma frflow_eq_is_iff (P Q : Prop) : (P = Q) = (P <-> Q).
Proof.
  apply propositional_extensionality. split; [intros ->; tauto | apply propositional_extensionality].
Qed.

(** The lemmas on membership and on equal propositions, where a quantifier binds what they speak of. *)
Ltac frflow_under := repeat first
  [ progress (setoid_rewrite in_app_iff)
  | progress (setoid_rewrite List_filter_In)
  | progress (setoid_rewrite frflow_eq_is_iff)
  | match goal with H : _ |- _ => progress (setoid_rewrite in_app_iff in H) end
  | match goal with H : _ |- _ => progress (setoid_rewrite List_filter_In in H) end
  | match goal with H : _ |- _ => progress (setoid_rewrite frflow_eq_is_iff in H) end ].

Ltac frflow_simpl :=
  repeat (progress (autorewrite with frflow in *; cbn in *; frflow_split; subst; frflow_under)).

Ltac frflow_refute search := solve [match goal with H : ~ _ |- _ =>
  exfalso; apply H; eexists; split; [ solve [search] | first [reflexivity | lia] ] end].

Ltac frflow_close := first
  [ lia | tauto | congruence
  | solve [intuition (subst; cbn in *; try lia; try congruence; eauto 8)]
  | solve [firstorder (subst; cbn in *; try lia; try congruence; eauto 8)]
  | solve [apply propositional_extensionality; firstorder (subst; cbn in *; try lia; try congruence; eauto 8)]
  (* a hypothesis says there is no such thing, and there is one: found by a search of growing depth, since a
     deeper search may settle on a witness the rest does not hold of *)
  | frflow_refute ltac:(eauto 4) | frflow_refute ltac:(eauto 6) | frflow_refute ltac:(eauto 8) ].

Lemma frflow_eq_iff (P Q : Prop) : P = Q -> (P <-> Q).
Proof. intros ->. tauto. Qed.
Ltac frflow_props := repeat match goal with
  | |- _ /\ _ => split
  | |- @eq Prop _ _ => apply propositional_extensionality
  | H : @eq Prop _ _ |- _ => apply frflow_eq_iff in H
  | H : ~ ~ _ |- _ => apply NNPP in H
  end.

(** The tactic tried first on every obligation: it unfolds the generated definitions, takes each `if` by cases,
    rewrites with the list lemmas above, and closes what remains by arithmetic and first-order search. *)
Ltac frflow_auto :=
  intros; repeat (autounfold with frflow_defs in *; intros); cbv zeta in *;
  repeat (progress (frflow_props; frflow_simpl)); frflow_props;
  frflow_close.

(** What is left of a statement about the theory as a whole once its witnesses are given. *)
(** One part of what an anonymous constructor gives: a witness of an `exists`, or a proof of a conjunct. *)
Ltac frflow_give x := first [ exists x | split; [ exact x | ] | exact x ].

Ltac frflow_witness :=
  repeat (autounfold with frflow_defs in *; intros); cbn in *; frflow_simpl;
  first [ reflexivity | frflow_close ].
