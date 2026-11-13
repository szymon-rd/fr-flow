package frflow.proof.prover.term

import frflow.core.term.algebra.{Maps, Sets}
import frflow.core.ty.Ty
import frflow.proof.prover.ast.*
import frflow.proof.prover.lower.{Atoms, Seen, Shape}

/** Maps and sets as the prover's functions (`K → Option V`, `A → Prop`): a key's value is the map applied
  * (`(m k)`), a member the set applied; a map updated, a set grown and a union are functions of a new variable
  * (`(fun k => if (k = key) then (some v) else (m k))`).
  */
trait ProverFinite[E] extends Maps[ProverTerm.S[E]], Sets[ProverTerm.S[E]]:
  protected def syntax: Syntax[E]
  protected def seen: Seen[E]
  protected def atoms: Atoms[E]
  private type S[A] = Scope => E

  /** `f` applied to `a`, flattened onto a call in parentheses (`(Rooms.covers b t)`). */
  protected def applied(f: E, a: E): E = seen.shape(f) match
    case Shape.Call(g, as) => syntax.paren(syntax.app(g, as :+ a))
    case _                 => atoms.call(f, List(a))

  def get[K, V](m: S[Map[K, V]], k: S[K]): S[Option[V]] = s => applied(m(s), k(s))
  def getOrElseAt[K, V](m: S[Map[K, V]], k: S[K], default: S[V]): S[V] =
    s => atoms.call(atoms.const("Option.getD"), List(applied(m(s), k(s)), default(s)))
  def updated[K, V](m: S[Map[K, V]], k: S[K], v: S[V]): S[Map[K, V]] = s =>
    val (map, key, value) = (m(s), k(s), v(s))
    over("k", s, map, key, value)(n => syntax.cond(syntax.paren(syntax.infix(LOp.Eq, n, key)),
      atoms.call(atoms.name("some"), List(value)), applied(map, n)))
  def member[A](set: S[Set[A]], x: S[A]): S[Boolean] = s => applied(set(s), x(s))
  def incl[A](set: S[Set[A]], x: S[A]): S[Set[A]] = s =>
    val (a, y) = (set(s), x(s))
    over("y", s, a, y)(n => syntax.infix(LOp.Or, syntax.paren(syntax.infix(LOp.Eq, n, y)), applied(a, n)))
  def union[A](set: S[Set[A]], other: S[Set[A]]): S[Set[A]] = s =>
    val (a, b) = (set(s), other(s))
    over("y", s, a, b)(n => syntax.infix(LOp.Or, applied(a, n), applied(b, n)))

  /** `(fun n => body)`, `n` a name none of `around` uses. Its type is the prover's to infer, so the binder's is
    * not told.
    */
  private def over(hint: String, s: Scope, around: E*)(body: E => E): E =
    val (n, _) = s.bind(hint, Ty.Unit, around.flatMap(seen.names).toSet)
    syntax.paren(syntax.fun(List(Binding.Bare(n)), body(syntax.name(n))))
