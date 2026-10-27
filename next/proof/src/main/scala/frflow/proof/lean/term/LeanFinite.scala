package frflow.proof.lean.term

import frflow.core.term.algebra.{Maps, Sets}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Atoms, LExprs}

/** Maps and sets as Lean's functions (`K → Option V`, `A → Prop`): a key's value is the map applied (`(m k)`), a
  * member the set applied; a map updated, a set grown and a union are functions of a new variable
  * (`(fun k => if (k = key) then (some v) else (m k))`).
  */
trait LeanFinite extends Maps[LeanTerm.S], Sets[LeanTerm.S]:
  import Atoms.{call, const, name}
  import LExpr.{Infix, Paren}
  private type S[A] = LeanTerm.S[A]

  def get[K, V](m: S[Map[K, V]], k: S[K]): S[Option[V]] = s => LeanTerm.applied(m(s), k(s))
  def getOrElseAt[K, V](m: S[Map[K, V]], k: S[K], default: S[V]): S[V] =
    s => call(const("Option.getD"), List(LeanTerm.applied(m(s), k(s)), default(s)))
  def updated[K, V](m: S[Map[K, V]], k: S[K], v: S[V]): S[Map[K, V]] = s =>
    val (map, key, value) = (m(s), k(s), v(s))
    over("k", s, map, key, value)(n => LExpr.If(Paren(Infix(LOp.Eq, n, key)), call(name("some"), List(value)),
      LeanTerm.applied(map, n)))
  def member[A](set: S[Set[A]], x: S[A]): S[Boolean] = s => LeanTerm.applied(set(s), x(s))
  def incl[A](set: S[Set[A]], x: S[A]): S[Set[A]] = s =>
    val (a, y) = (set(s), x(s))
    over("y", s, a, y)(n => Infix(LOp.Or, Paren(Infix(LOp.Eq, n, y)), LeanTerm.applied(a, n)))
  def union[A](set: S[Set[A]], other: S[Set[A]]): S[Set[A]] = s =>
    val (a, b) = (set(s), other(s))
    over("y", s, a, b)(n => Infix(LOp.Or, LeanTerm.applied(a, n), LeanTerm.applied(b, n)))

  /** `(fun n => body)`, `n` a name none of `around` uses. Its type is Lean's to infer, so the binder's is not told. */
  private def over(hint: String, s: Scope, around: LExpr*)(body: LExpr => LExpr): LExpr =
    val (n, _) = s.bind(hint, Ty.Unit, around.flatMap(LExprs.identifiers).toSet)
    Paren(LExpr.Fun(List(LBinder.Bare(n)), body(LExpr.Name(n))))
