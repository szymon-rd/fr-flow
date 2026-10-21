/-!
# FrFlow kernel: semantics of Scala types

FrFlow translates the Scala definitions of a model to Lean. This file gives the
meaning of the Scala types that have no direct Lean counterpart. It is part of
the trusted base: a wrong definition here would make proofs about the
generated Lean say nothing about the Scala program.

- `Boolean` is `Prop` (no definition needed).
- `Int`, `Long` and `BigInt` are `Int`: the translation assumes no overflow.
- `scala.collection.immutable.Map[K, V]` is a partial function `K → Option V`.
- `scala.collection.immutable.Set[A]` is a predicate `A → Prop`.

Both collections are compared extensionally, as Scala compares them with `==`.
-/

noncomputable section
open Classical

namespace FrFlow.Scala

/-- `scala.collection.immutable.Map[K, V]`. -/
abbrev Map (K V : Type) : Type := K → Option V

/-- `scala.collection.immutable.Set[A]`. -/
abbrev Set (A : Type) : Type := A → Prop

namespace Map
variable {K V : Type}

/-- `Map.empty` -/
def empty : Map K V := fun _ => none

/-- `m.updated(k, v)`, `m + (k -> v)` -/
def updated (m : Map K V) (k : K) (v : V) : Map K V := fun k' => if k' = k then some v else m k'

/-- `m.removed(k)`, `m - k` -/
def removed (m : Map K V) (k : K) : Map K V := fun k' => if k' = k then none else m k'

/-- `m.keySet` -/
def keySet (m : Map K V) : Set K := fun k => m k ≠ none

@[simp] theorem empty_apply (k : K) : (empty : Map K V) k = none := rfl
@[simp] theorem updated_apply (m : Map K V) (k k' : K) (v : V) :
    m.updated k v k' = if k' = k then some v else m k' := rfl
@[simp] theorem removed_apply (m : Map K V) (k k' : K) :
    m.removed k k' = if k' = k then none else m k' := rfl
@[simp] theorem keySet_apply (m : Map K V) (k : K) : m.keySet k = (m k ≠ none) := rfl

end Map

namespace Set
variable {A : Type}

/-- `Set.empty` -/
def empty : Set A := fun _ => False

/-- `Set(a, b, ...)` -/
def ofList (l : List A) : Set A := fun x => x ∈ l

/-- `s + a` -/
def incl (s : Set A) (a : A) : Set A := fun x => x = a ∨ s x

/-- `s - a` -/
def excl (s : Set A) (a : A) : Set A := fun x => x ≠ a ∧ s x

/-- `s ++ t`, `s.union(t)` -/
def union (s t : Set A) : Set A := fun x => s x ∨ t x

/-- `s.intersect(t)` -/
def inter (s t : Set A) : Set A := fun x => s x ∧ t x

/-- `s.diff(t)`, `s -- t` -/
def diff (s t : Set A) : Set A := fun x => s x ∧ ¬t x

@[simp] theorem empty_apply (a : A) : (empty : Set A) a = False := rfl
@[simp] theorem ofList_apply (l : List A) (a : A) : ofList l a = (a ∈ l) := rfl
@[simp] theorem incl_apply (s : Set A) (a x : A) : s.incl a x = (x = a ∨ s x) := rfl
@[simp] theorem excl_apply (s : Set A) (a x : A) : s.excl a x = (x ≠ a ∧ s x) := rfl
@[simp] theorem union_apply (s t : Set A) (x : A) : s.union t x = (s x ∨ t x) := rfl
@[simp] theorem inter_apply (s t : Set A) (x : A) : s.inter t x = (s x ∧ t x) := rfl
@[simp] theorem diff_apply (s t : Set A) (x : A) : s.diff t x = (s x ∧ ¬t x) := rfl

end Set

end FrFlow.Scala
