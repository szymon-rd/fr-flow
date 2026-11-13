package frflow.proof.prover.term

import cats.Monoid
import frflow.proof.prover.ast.*

/** A reading of the syntax that gathers: each form is what its parts are, joined in the order written, and a form
  * with no parts nothing. An analysis is one of these saying what the forms it is about are (`layout.Mentions`,
  * `Identifiers`).
  */
abstract class Gathered[M](using M: Monoid[M]) extends Syntax[M]:
  protected def all(parts: List[M]): M = M.combineAll(parts)
  protected def binding(b: Binding[M]): M = b match
    case Binding.Explicit(_, t) => t
    case Binding.Several(_, t)  => t
    case Binding.Implicit(_, t) => t
    case Binding.Instance(c)    => c
    case Binding.Bare(_)        => M.empty
    case Binding.Of(_, t)       => t
    case Binding.Member(_, in)  => in
  private def bound(params: List[Binding[M]], body: M): M = all(params.map(binding) :+ body)

  def name(n: ProverName): M = M.empty
  def const(path: List[ProverName]): M = M.empty
  def ctor(data: ProverName, ctor: ProverName): M = M.empty
  def num(n: BigInt): M = M.empty
  def str(s: String): M = M.empty
  def app(fn: M, args: List[M]): M = all(fn :: args)
  def infix(op: LOp, left: M, right: M): M = all(List(left, right))
  def prefix(op: LPrefix, arg: M): M = arg
  def paren(inner: M): M = inner
  def dot(on: M, field: String): M = on
  def tuple(elems: List[M]): M = all(elems)
  def listLit(elems: List[M]): M = all(elems)
  def update(record: M, fields: List[(ProverName, M)]): M = all(record :: fields.map(_._2))
  def fun(params: List[Binding[M]], body: M): M = bound(params, body)
  def forall(params: List[Binding[M]], body: M): M = bound(params, body)
  def exists(params: List[Binding[M]], body: M): M = bound(params, body)
  def cond(c: M, ifTrue: M, ifFalse: M): M = all(List(c, ifTrue, ifFalse))
  def matching(on: M, arms: List[(M, M)]): M = all(on :: arms.flatMap((p, b) => List(p, b)))
  def let(name: ProverName, ty: M, value: M, body: M): M = all(List(ty, value, body))
  def typed(e: M, ty: M): M = all(List(e, ty))
  def anonymous(elems: List[M]): M = all(elems)
  def by(tactic: ProverName): M = M.empty
  def named(fn: M, name: ProverName, value: M): M = all(List(fn, value))
