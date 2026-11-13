package frflow.proof.prover.term

import frflow.proof.prover.ast.*
import frflow.proof.prover.lower.{Identifiers, Seen, Shape}

/** A term of any syntax with what it is beside it. What a syntax makes of a term (`E`: a text, say) cannot be read
  * back, so the one writing keeps, of each term written, the little the lowering asks of it (`Seen`): its shape,
  * one level of it, and the identifiers it names. With it the lowering writes straight into any syntax, no tree
  * between: LNCS 7470's interpreter that carries what an optimization reads beside its result.
  */
final case class Shaped[E](e: E, shape: Shape[Shaped[E]], names: Set[String])

object Shaped:
  given seen[E]: Seen[Shaped[E]] with
    def shape(t: Shaped[E]): Shape[Shaped[E]] = t.shape
    def names(t: Shaped[E]): Set[String] = t.names

  /** Any syntax, writing each term with what it is. */
  given syntax[E](using base: Syntax[E]): Syntax[Shaped[E]] = Shapes(base)

/** `base`, each term it writes kept with its shape and its identifiers (`Identifiers`, read as it is written). */
final class Shapes[E](base: Syntax[E]) extends Syntax[Shaped[E]]:
  private type T = Shaped[E]
  private def plain(e: E, names: Set[String]): T = Shaped(e, Shape.Other, names)
  private def es(ts: List[T]): List[E] = ts.map(_.e)
  private def ns(ts: List[T]): List[Set[String]] = ts.map(_.names)
  private def bound(ps: List[Binding[T]]): List[Binding[E]] = ps.map(_.map(_.e))

  def name(n: ProverName): T = plain(base.name(n), Identifiers.name(n))
  def const(path: List[ProverName]): T = plain(base.const(path), Identifiers.const(path))
  def ctor(data: ProverName, ctor: ProverName): T =
    Shaped(base.ctor(data, ctor), Shape.Ctor(data), Identifiers.ctor(data, ctor))
  def num(n: BigInt): T = plain(base.num(n), Set.empty)
  def str(s: String): T = plain(base.str(s), Set.empty)
  def app(fn: T, args: List[T]): T =
    Shaped(base.app(fn.e, es(args)), Shape.Applied(fn, args), Identifiers.app(fn.names, ns(args)))
  def infix(op: LOp, left: T, right: T): T = plain(base.infix(op, left.e, right.e), left.names ++ right.names)
  def prefix(op: LPrefix, arg: T): T = plain(base.prefix(op, arg.e), arg.names)
  def paren(inner: T): T = Shaped(base.paren(inner.e), inner.shape match
    case Shape.Applied(fn, args) => Shape.Call(fn, args)
    case _                       => Shape.Other, inner.names)
  def dot(on: T, field: String): T = plain(base.dot(on.e, field), on.names)
  def tuple(elems: List[T]): T = plain(base.tuple(es(elems)), Identifiers.tuple(ns(elems)))
  def listLit(elems: List[T]): T =
    Shaped(base.listLit(es(elems)), Shape.Listed(elems), Identifiers.listLit(ns(elems)))
  def update(record: T, fields: List[(ProverName, T)]): T =
    plain(base.update(record.e, fields.map((n, v) => n -> v.e)), Set.empty)
  def fun(params: List[Binding[T]], body: T): T = plain(base.fun(bound(params), body.e), Set.empty)
  def forall(params: List[Binding[T]], body: T): T = plain(base.forall(bound(params), body.e), Set.empty)
  def exists(params: List[Binding[T]], body: T): T = plain(base.exists(bound(params), body.e), Set.empty)
  def cond(c: T, ifTrue: T, ifFalse: T): T =
    plain(base.cond(c.e, ifTrue.e, ifFalse.e), c.names ++ ifTrue.names ++ ifFalse.names)
  def matching(on: T, arms: List[(T, T)]): T =
    plain(base.matching(on.e, arms.map((p, b) => p.e -> b.e)), Set.empty)
  def let(name: ProverName, ty: T, value: T, body: T): T = plain(base.let(name, ty.e, value.e, body.e), Set.empty)
  def typed(e: T, ty: T): T = Shaped(base.typed(e.e, ty.e), Shape.Typed(e.shape match
    case Shape.Listed(Nil) => true
    case _                 => false), e.names ++ ty.names)
  def anonymous(elems: List[T]): T = plain(base.anonymous(es(elems)), Set.empty)
  def by(tactic: ProverName): T = plain(base.by(tactic), Set.empty)
  def named(fn: T, name: ProverName, value: T): T = plain(base.named(fn.e, name, value.e), Set.empty)
