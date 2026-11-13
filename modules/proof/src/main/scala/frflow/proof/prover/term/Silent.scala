package frflow.proof.prover.term

import frflow.proof.prover.ast.*

/** A reading of the syntax that says `none` of every form: one that asks of a few forms only says what those are
  * (`layout.Params`, a statement's top; `audit.Assumed`, where a constant is assumed).
  */
abstract class Silent[A](none: A) extends Syntax[A]:
  def name(n: ProverName): A = none
  def const(path: List[ProverName]): A = none
  def ctor(data: ProverName, ctor: ProverName): A = none
  def num(n: BigInt): A = none
  def str(s: String): A = none
  def app(fn: A, args: List[A]): A = none
  def infix(op: LOp, left: A, right: A): A = none
  def prefix(op: LPrefix, arg: A): A = none
  def paren(inner: A): A = none
  def dot(on: A, field: String): A = none
  def tuple(elems: List[A]): A = none
  def listLit(elems: List[A]): A = none
  def update(record: A, fields: List[(ProverName, A)]): A = none
  def fun(params: List[Binding[A]], body: A): A = none
  def forall(params: List[Binding[A]], body: A): A = none
  def exists(params: List[Binding[A]], body: A): A = none
  def cond(c: A, ifTrue: A, ifFalse: A): A = none
  def matching(on: A, arms: List[(A, A)]): A = none
  def let(name: ProverName, ty: A, value: A, body: A): A = none
  def typed(e: A, ty: A): A = none
  def anonymous(elems: List[A]): A = none
  def by(tactic: ProverName): A = none
  def named(fn: A, name: ProverName, value: A): A = none
