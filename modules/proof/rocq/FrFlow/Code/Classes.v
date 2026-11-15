(** What the classes of the code read have, decided by computing over the table of the code: so that a proof
    is not asked it of each value. *)

From Stdlib Require Import String List Bool.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Import ListNotations.

Fixpoint lines_of (T : table) : list (string * list string) :=
  match T with
  | Table _ _ lines _ => lines
  | Extend T' more => lines_of T' ++ lines_of more
  end.

Lemma assoc_in {A : Type} (xs : list (string * A)) (k : string) (a : A) : assoc xs k = Some a -> In k (map fst xs).
Proof.
  induction xs as [| [k' a'] rest IH]; cbn; [discriminate |].
  destruct (String.eqb_spec k' k) as [-> | _]; [left; reflexivity | right; auto].
Qed.

Lemma class_in_known (T : table) (cls : string) (c : tree) : class_in T cls = Some c -> In cls (map fst (classes_of T)).
Proof.
  induction T as [classes members lines modules | T' IH1 more IH2]; cbn.
  - apply assoc_in.
  - rewrite map_app, in_app_iff. destruct (class_in T' cls) eqn:E; [left; eauto | right; auto].
Qed.

Lemma line_in_known (T : table) (cls : string) (l : list string) : line_in T cls = Some l -> In cls (map fst (lines_of T)).
Proof.
  induction T as [classes members lines modules | T' IH1 more IH2]; cbn.
  - apply assoc_in.
  - rewrite map_app, in_app_iff. destruct (line_in T' cls) eqn:E; [left; eauto | right; auto].
Qed.

(** No class of the code has a method that runs when `s` is called: computed. *)
Definition unimplemented (T : table) (s : sym) : bool :=
  forallb (fun k => match impl T k s with None => true | Some _ => false end)
    (map fst (lines_of T) ++ map fst (classes_of T)).

Lemma impl_none (T : table) (s : sym) (cls : string) : unimplemented T s = true -> impl T cls s = None.
Proof.
  intros H. unfold unimplemented in H. rewrite forallb_forall in H.
  destruct (in_dec string_dec cls (map fst (lines_of T) ++ map fst (classes_of T))) as [Hin | Hout].
  - specialize (H cls Hin). destruct (impl T cls s); [discriminate | reflexivity].
  - rewrite in_app_iff in Hout. unfold impl, own.
    assert (line_in T cls = None) as ->.
    { destruct (line_in T cls) eqn:E; [| reflexivity]. exfalso. apply Hout. left. exact (line_in_known _ _ _ E). }
    assert (class_of T cls = None) as Hc.
    { unfold class_of. destruct (foreign cls); [reflexivity |].
      destruct (class_in T cls) eqn:E; [| reflexivity]. exfalso. apply Hout. right. exact (class_in_known _ _ _ E). }
    destruct (foreign cls); cbn; rewrite Hc; reflexivity.
Qed.

(** A call of `s` on any value runs no method of the code. *)
Lemma implemented_none (T : table) (s : sym) (v : val) : unimplemented T s = true -> implemented T v s = None.
Proof.
  intros H. destruct v as [| | | | o | |]; try reflexivity. destruct o; try reflexivity. cbn. exact (impl_none _ _ _ H).
Qed.
