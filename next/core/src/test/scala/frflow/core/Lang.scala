package frflow.core

import frflow.core.expr.Value
import frflow.core.name.SymbolName
import frflow.core.term.{Bound, Final, Sym}
import frflow.core.ty.{NumKind, Ty}

/** The algebras over one interpreter, with short names for the tests' formulas: what the DSL gives a model. */
final class Lang[T[_]](val s: Sym[T]):
  def sym[A](name: String, ty: Ty): T[A] = s.param(SymbolName(name), ty)
  def num(n: Int): T[BigInt] = s.lit(BigInt(n), Value.Num(n), Lang.big)
  def str(v: String): T[String] = s.lit(v, Value.Str(v), Ty.Str)
  def truth: T[Boolean] = s.bool(true)
  def forall[A](hint: String, ty: Ty)(p: T[A] => T[Boolean]): T[Boolean] = s.forall(Bound(hint, ty))(p)
  def call[A, B](f: T[A => B], a: T[A]): T[B] = s.app(f, a)
  def call2[A, B, C](f: T[A => B => C], a: T[A], b: T[B]): T[C] = s.app(s.app(f, a), b)

object Lang:
  val big: Ty = Ty.Num(NumKind.Big)

  /** A formula, the same term for every interpreter. */
  def formula(f: [T[_]] => Lang[T] => T[Boolean]): Final[Boolean] = [T[_]] => (s: Sym[T]) => f[T](Lang(s))

  val truth: Final[Boolean] = formula([T[_]] => (l: Lang[T]) => l.truth)
