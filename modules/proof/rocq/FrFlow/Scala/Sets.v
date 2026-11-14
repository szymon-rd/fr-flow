(** What the protocol of a concurrent set (`Jdk.concurrent_set`) gives for each of its methods, said as a
    proof uses it: by what the set holds after the call, not by how the protocol computes it. *)

From Stdlib Require Import String List Bool.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine FrFlow.Scala.Tree FrFlow.Scala.Value FrFlow.Scala.Jdk.
Import ListNotations.
Open Scope string_scope.

(** The one argument of a call, typed as the machine has its values, so that a rule's statement can be rewritten
    with a fact here. *)
Local Notation one x := (@cons (Machine.val code obj) x (@nil (Machine.val code obj))).

Lemma holds_in (xs : list val) (x : val) : holds xs x = true <-> In x xs.
Proof.
  unfold holds. rewrite existsb_exists. split.
  - intros (y & Hy & E). unfold val_eqb in E. destruct (val_eq_dec x y) as [-> |]; [exact Hy | discriminate].
  - intros H. exists x. split; [exact H |]. unfold val_eqb. destruct (val_eq_dec x x); [reflexivity | contradiction].
Qed.

Lemma without_in (xs : list val) (x y : val) : In y (without xs x) <-> In y xs /\ y <> x.
Proof.
  unfold without. rewrite filter_In. unfold val_eqb. destruct (val_eq_dec x y) as [-> | Hne]; simpl.
  - split; [intros [_ H]; discriminate | intros [_ H]; contradiction].
  - split; [intros [H _]; split; [exact H | intros ->; contradiction] | intros [H _]; split; [exact H | reflexivity]].
Qed.

(** `add`: the set holds what it held and what was added. *)
Lemma set_add (t : tid) (intr : bool) (held : list val) (x : val) (choice : nat) :
  exists b held', p_call concurrent_set "add" t intr held (one x) choice = Gives (inr (VBool b)) held' /\
    (forall y, In y held' <-> In y held \/ y = x).
Proof.
  cbn. destruct (holds held x) eqn:E.
  - exists false, held. split; [reflexivity |]. apply holds_in in E.
    intros y. split; [tauto | intros [H | ->]; assumption].
  - exists true, (held ++ [x])%list. split; [reflexivity |]. intros y. rewrite in_app_iff. cbn.
    split; [intros [H | [-> | []]]; tauto | intros [H | ->]; tauto].
Qed.

(** `remove`: the set holds what it held but what was removed. *)
Lemma set_remove (t : tid) (intr : bool) (held : list val) (x : val) (choice : nat) :
  exists b held', p_call concurrent_set "remove" t intr held (one x) choice = Gives (inr (VBool b)) held' /\
    (forall y, In y held' <-> In y held /\ y <> x).
Proof. exists (holds held x), (without held x). split; [reflexivity | intros y; apply without_in]. Qed.

Lemma set_isEmpty (t : tid) (intr : bool) (held : list val) (choice : nat) :
  p_call concurrent_set "isEmpty" t intr held [] choice =
    Gives (inr (VBool (match held with [] => true | _ => false end))) held.
Proof. reflexivity. Qed.

Lemma set_contains (t : tid) (intr : bool) (held : list val) (x : val) (choice : nat) :
  p_call concurrent_set "contains" t intr held (one x) choice = Gives (inr (VBool (holds held x))) held.
Proof. reflexivity. Qed.

(** `next`, of a traversal: nothing, or something the set holds that the traversal has not passed. *)
Lemma set_next (t : tid) (intr : bool) (held passed : list val) (choice : nat) :
  exists y, p_call concurrent_set "next" t intr held (one (VList passed)) choice = Gives (inr y) held /\
    (y = vnone \/ exists x, y = vsome x /\ In x held /\ ~ In x passed).
Proof.
  cbn. eexists. split; [reflexivity |].
  destruct (nth_error _ _) as [y |] eqn:E; [right | left; reflexivity].
  exists y. split; [reflexivity |]. apply nth_error_In in E. apply filter_In in E as [H Hn].
  split; [exact H |]. intros Hp. apply holds_in in Hp. rewrite Hp in Hn. discriminate.
Qed.
