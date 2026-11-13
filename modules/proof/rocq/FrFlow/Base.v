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

(** The definitions FrFlow generates: `frflow_auto` unfolds them. Each is marked as one (`Frflow_def`), so that
    running code tells a generated definition from the standard library's. *)
Create HintDb frflow_defs.
#[global] Hint Unfold decide List_map List_flatMap List_zip List_Nodup Option_getD : frflow_defs.
Class Frflow_def {A : Type} (f : A) : Prop := frflow_def : True.
#[global] Instance : Frflow_def (@decide) := I.
#[global] Instance : Frflow_def (@List_map) := I.
#[global] Instance : Frflow_def (@List_flatMap) := I.
#[global] Instance : Frflow_def (@List_zip) := I.
#[global] Instance : Frflow_def (@List_Nodup) := I.
#[global] Instance : Frflow_def (@Option_getD) := I.

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

(** What is known by cases, taken by cases: a hypothesis that is one of several things (a step that is one of a
    run's steps), and an option matched on (what a schedule says the others left, if anything). *)
Ltac frflow_cases := repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | H : False |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- context [match ?o with Some _ => _ | None => _ end] => destruct o eqn:?
  | H : context [match ?o with Some _ => _ | None => _ end] |- _ => destruct o eqn:?
  end.

Ltac frflow_simpl :=
  repeat (progress (autorewrite with frflow in *; cbn in *; frflow_split; subst; frflow_under; frflow_cases)).

Ltac frflow_refute search := solve [match goal with H : ~ _ |- _ =>
  exfalso; apply H; eexists; split; [ solve [search] | first [reflexivity | lia] ] end].

(** What holds of every member of a list written out holds of each of them. *)
Lemma frflow_all_cons {A : Type} (x : A) (R P : A -> Prop) :
  (forall b, x = b \/ R b -> P b) -> P x /\ (forall b, R b -> P b).
Proof. intros H. split; [apply H; left; reflexivity | intros b r; apply H; right; exact r]. Qed.
Ltac frflow_members := repeat match goal with
  | H : forall b, ?x = b \/ _ -> _ |- _ => apply frflow_all_cons in H; destruct H as [? H]; cbn beta in *
  | H : forall b, False -> _ |- _ => clear H
  end.

Lemma List_Pairwise_nil {A : Type} (p : A -> A -> Prop) : List_Pairwise p [].
Proof. constructor. Qed.

(** A statement about values written out (an example): a pair by its parts, a proposition equal to another by
    each giving the other; what is said of every member of a list is refuted by one member, or shown of each; what
    is left is arithmetic or names that differ. *)
Ltac frflow_leaf := first
  [ reflexivity | lia | congruence | tauto
  | solve [firstorder (subst; cbn in *; first [lia | congruence])] ].
Ltac frflow_one_member H := first
  [ solve [let h := fresh "h" in pose proof (proj1 (frflow_all_cons _ _ _ H)) as h; cbn in h; frflow_leaf]
  | apply frflow_all_cons in H; destruct H as [_ H]; cbn beta in H; frflow_one_member H ].
Ltac frflow_values :=
  unfold not in *; intros;
  repeat match goal with
    | |- (_, _) = (_, _) => apply f_equal2
    | |- @eq Prop _ _ => apply propositional_extensionality; split; intros
    | |- _ /\ _ => split
    | |- forall _, _ => intros
    end;
  cbn in *;
  first
    [ frflow_leaf
    | solve [match goal with H : forall b, _ = b \/ _ -> _ |- _ => frflow_one_member H end]
    | solve [frflow_cases; subst; cbn in *; frflow_leaf]
    | solve [exfalso; match goal with H : _ -> False |- _ => apply H end;
             intros; frflow_cases; subst; cbn in *; frflow_leaf] ].

Lemma frflow_eq_iff (P Q : Prop) : P = Q -> (P <-> Q).
Proof. intros ->. tauto. Qed.
Ltac frflow_props := repeat match goal with
  | |- _ /\ _ => split
  | |- @eq Prop _ _ => apply propositional_extensionality
  | H : @eq Prop _ _ |- _ => apply frflow_eq_iff in H
  | H : ~ ~ _ |- _ => apply NNPP in H
  end.

(** What a claim taken as given says is equal (or each the other's condition), rewritten in the goal and in what is
    known, its own conditions met by what is known: the answer of a call a class makes of what it holds, by the
    claims on it. Only a claim that ends in an equation is rewritten with: Rocq would rewrite with an order too. *)
Ltac frflow_given := first [eassumption | solve [repeat split; eassumption]].
Ltac frflow_equation H := lazymatch type of H with
  | forall a, _ = _ => idtac | forall a b, _ = _ => idtac | forall a b c, _ = _ => idtac
  | forall a b c d, _ = _ => idtac | forall a b c d e, _ = _ => idtac | forall a b c d e f, _ = _ => idtac
  | forall a, _ <-> _ => idtac | forall a b, _ <-> _ => idtac | forall a b c, _ <-> _ => idtac
  | forall a b c d, _ <-> _ => idtac | forall a b c d e, _ <-> _ => idtac | forall a b c d e f, _ <-> _ => idtac
  end.
Ltac frflow_rewrite := do 8 (try match goal with
  | H : forall _, _ |- _ => frflow_equation H; erewrite H by frflow_given
  | H : forall _, _, h : _ |- _ => frflow_equation H; erewrite H in h by frflow_given
  end).
(** A claim taken as given that gives the goal, its conditions met by what is known or by what the claims say is
    equal: what a call keeps, by the claim that the call of what the class holds keeps it. *)
Ltac frflow_side := first [ frflow_given | lia | solve [frflow_rewrite; first [ lia | eassumption ]] ].
Ltac frflow_backward := solve [
  frflow_rewrite; first [ lia | eassumption
  | match goal with H : forall _, _ |- _ => eapply H; clear H; frflow_side end ] ].

Ltac frflow_close := first
  [ lia | tauto | congruence
  | solve [intuition (subst; cbn in *; try lia; try congruence; eauto 8)]
  | solve [firstorder (subst; cbn in *; try lia; try congruence; eauto 8)]
  | solve [apply propositional_extensionality; firstorder (subst; cbn in *; try lia; try congruence; eauto 8)]
  (* a hypothesis says there is no such thing, and there is one: found by a search of growing depth, since a
     deeper search may settle on a witness the rest does not hold of *)
  | frflow_refute ltac:(eauto 4) | frflow_refute ltac:(eauto 6) | frflow_refute ltac:(eauto 8)
  (* what the claims taken as given say is equal, put in its place *)
  | solve [frflow_rewrite; frflow_simpl; frflow_props; frflow_leaf]
  | frflow_backward
  (* a statement about values written out *)
  | solve [frflow_values] ].

(** The tactic tried first on every obligation: it unfolds the generated definitions, takes each `if` by cases,
    rewrites with the list lemmas above, and closes what remains by arithmetic and first-order search. *)
Ltac frflow_auto :=
  intros; repeat (autounfold with frflow_defs in *; intros); cbv zeta in *;
  repeat (progress (frflow_props; frflow_simpl)); frflow_props;
  frflow_close.

(** What is left of a statement about the theory as a whole once its witnesses are given. *)
(** One part of what an anonymous constructor gives: a witness of an `exists`, or a proof of a conjunct. *)
Ltac frflow_give x := first [ exists x | split; [ exact x | ] | exact x ].

(** An example: the code run on the values it gives, as code runs. `unfold` puts a `let`'s value wherever it is
    read, so a step of the code would be computed once for each reading of its result; here a call is run when what
    it is given is computed, each `let` of it once, before what follows it (`frflow_cbv`), and an `if` is decided,
    not taken by cases. A generated definition is put in place of its name with every `let` kept (`cbv delta`). *)
Create Rewrite HintDb frflow_eval.
#[global] Hint Rewrite @List_filter_cons @List_filter_nil @List_foldl_cons @List_foldl_nil : frflow_eval.

Ltac frflow_head t := lazymatch t with ?f _ => frflow_head f | _ => t end.
Ltac frflow_is_def f := is_const f; let _ := constr:(_ : Frflow_def f) in idtac.
Ltac frflow_code := repeat match goal with
  | |- context [?f] => frflow_is_def f; progress (cbv beta delta [f])
  end.

Lemma frflow_ex_tail {A : Type} (a : A) (R Q : A -> Prop) :
  (exists d, R d /\ Q d) -> exists d, (a = d \/ R d) /\ Q d.
Proof. intros [d [r q]]. exists d. split; [right; exact r | exact q]. Qed.
Lemma frflow_each_cons {A : Type} (a : A) (R Q : A -> Prop) :
  Q a -> (forall x, R x -> Q x) -> forall x, a = x \/ R x -> Q x.
Proof. intros qa rest x [<- | r]; [exact qa | exact (rest x r)]. Qed.

(** Code to run: a `let`, or a generated definition given all it takes. *)
Ltac frflow_is_call t :=
  lazymatch t with
  | (let _ := _ in _) => idtac
  | ?f _ => let h := frflow_head f in frflow_is_def h;
      let T := type of t in lazymatch T with (forall _, _) => fail | _ => idtac end
  end.

(** A proposition about values written out, shown (`frflow_true`) or refuted (`frflow_false`) by its form: the
    code in it run first (`frflow_run`), a member of a list written out taken one at a time. *)
Ltac frflow_true :=
  frflow_run; repeat (progress (autorewrite with frflow_eval; cbn; frflow_decide_goal)); cbn;
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; frflow_true
  | |- _ \/ _ => first [ solve [left; frflow_true] | solve [right; frflow_true] ]
  | |- ~ _ => let h := fresh "h" in intro h; frflow_false h
  | |- exists _, (_ = _ \/ _) /\ _ =>
      first [ solve [eexists; split; [left; reflexivity | frflow_true]] | apply frflow_ex_tail; frflow_true ]
  | |- forall x, _ = x \/ _ -> _ => apply frflow_each_cons; [ frflow_true | cbn beta; frflow_true ]
  | |- forall x, False -> _ => let x := fresh in let f := fresh in intros x f; destruct f
  | |- _ => first [ solve [frflow_values] | solve [frflow_code; cbv zeta; frflow_values] ]
  end
with frflow_false h :=
  revert h; frflow_run; repeat (progress (autorewrite with frflow_eval; cbn; frflow_decide_goal)); intro h;
  cbn in h;
  lazymatch type of h with
  | False => exact h
  | False /\ _ => destruct h as [[] _]
  | (_ = ?x \/ _) /\ _ =>
      let e := fresh "e" in let m := fresh "m" in let q := fresh "q" in
      destruct h as [[e | m] q];
      [ subst; frflow_false q | let h' := fresh "h" in pose proof (conj m q) as h'; frflow_false h' ]
  | _ /\ _ =>
      let a := fresh "h" in let b := fresh "h" in
      destruct h as [a b]; first [ solve [frflow_false a] | solve [frflow_false b] ]
  | _ \/ _ => destruct h as [h | h]; frflow_false h
  | ~ _ => apply h; frflow_true
  | exists _, _ => let x := fresh "x" in destruct h as [x h]; frflow_false h
  | forall b, _ = b \/ _ -> _ =>
      let a := fresh "h" in apply frflow_all_cons in h; destruct h as [a h]; cbn beta in *;
      first [ solve [frflow_false a] | solve [frflow_false h] ]
  | _ => first [ frflow_leaf | frflow_one_member h ]
  end
with frflow_decide_goal := repeat match goal with
  | |- context [ite ?P _ _] => first
      [ rewrite (ite_true P) by (solve [frflow_true])
      | rewrite (ite_false P) by (solve [let h := fresh "h" in intro h; frflow_false h]) ]
  end
with frflow_decide_in H := repeat match type of H with
  | context [ite ?P _ _] => first
      [ rewrite (ite_true P) in H by (solve [frflow_true])
      | rewrite (ite_false P) in H by (solve [let h := fresh "h" in intro h; frflow_false h]) ]
  end
(** `H : x = t`: `t` run as code runs: what a call is given first, each `let` once, before what follows it. *)
with frflow_cbv H :=
  lazymatch type of H with
  | _ = (let y := ?v in @?b y) =>
      let y' := fresh y in let Hy := fresh "E" in
      remember v as y' eqn:Hy in H;
      lazymatch type of H with ?x = _ => change (x = b y') in H end; cbv beta in H;
      frflow_cbv Hy; subst y'; frflow_cbv H
  | _ = ite ?P ?a ?b =>
      first [ rewrite (ite_true P a b) in H by (solve [frflow_true])
            | rewrite (ite_false P a b) in H by (solve [let h := fresh "h" in intro h; frflow_false h]) ];
      frflow_cbv H
  | _ = ?t =>
      tryif once (match t with
        | context [?u] => tryif constr_eq u t then fail else idtac; frflow_is_call u;
            let z := fresh "v" in let E := fresh "E" in
            remember u as z eqn:E in *; frflow_cbv E; subst z
        end)
      then frflow_cbv H
      else tryif (let f := frflow_head t in frflow_is_def f; lazymatch t with _ _ => idtac end)
        then (let f := frflow_head t in cbv beta delta [f] in H; frflow_cbv H)
        else (repeat (progress (autorewrite with frflow_eval in H; cbn in H; frflow_decide_in H));
          lazymatch type of H with
          | _ = (let _ := _ in _) => frflow_cbv H
          | _ = ite _ _ _ => frflow_cbv H
          | _ => idtac
          end)
  end
with frflow_run := repeat match goal with
  | |- context [?u] => frflow_is_call u;
      let z := fresh "run" in let E := fresh "R" in
      remember u as z eqn:E; frflow_cbv E; subst z
  end.

Ltac frflow_alone :=
  lazymatch goal with |- ?g => let f := frflow_head g in tryif frflow_is_def f then cbv beta delta [f] else idtac end;
  intros;
  repeat match goal with
    | H : ?T |- _ => let f := frflow_head T in frflow_is_def f; clear H
    end;
  repeat match goal with
    | x : ?T |- _ => lazymatch type of T with Prop => fail | _ => clear x end
    end;
  repeat match goal with H : _ |- _ => revert H end.

(** An example, or a condition whose values are given: asked under the claims, decided by running the code. *)
Ltac frflow_evaluate := frflow_alone; frflow_true.
(** Whether running the code refutes what is asked: then no search is made for a proof from the claims. *)
Ltac frflow_refuted :=
  assert_succeeds (frflow_alone; lazymatch goal with |- ?F => assert (~ F) by frflow_true end).
Ltac frflow_example := first [ solve [frflow_evaluate] | tryif frflow_refuted then fail else frflow_auto ].

Ltac frflow_witness := first
  [ solve [timeout 100 frflow_evaluate]
  | repeat (autounfold with frflow_defs in *; intros); cbn in *; frflow_simpl;
    first [ reflexivity | frflow_close
          | repeat match goal with |- _ /\ _ => split end;
            first [ reflexivity | apply List_Pairwise_nil | frflow_close ] ] ].
