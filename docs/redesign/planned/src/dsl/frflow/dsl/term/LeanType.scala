package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.build.Declarations

/** What a Scala type is in the IR, and the domain types it needs declared. */
trait LeanType[A]:
  def ty: Ty
  def declares: Declarations

object LeanType:
  def apply[A](using t: LeanType[A]): LeanType[A] = t
  def of[A](t: Ty, parts: LeanType[?]*): LeanType[A] = new LeanType[A]:
    val ty: Ty = t
    val declares: Declarations = parts.toList.foldMap(_.declares)

  given LeanType[Boolean] = of(Ty.Bool)
  given LeanType[String] = of(Ty.Str)
  given LeanType[Unit] = of(Ty.Unit)
  given LeanType[Int] = of(Ty.Num(NumKind.Int32))
  given LeanType[Long] = of(Ty.Num(NumKind.Int64))
  given LeanType[BigInt] = of(Ty.Num(NumKind.Big))
  given [A](using a: LeanType[A]): LeanType[List[A]] = of(Ty.ListOf(a.ty), a)
  given [A](using a: LeanType[A]): LeanType[Option[A]] = of(Ty.OptionOf(a.ty), a)
  given [K, V](using k: LeanType[K], v: LeanType[V]): LeanType[Map[K, V]] = of(Ty.MapOf(k.ty, v.ty), k, v)
  given [A, B](using a: LeanType[A], b: LeanType[B]): LeanType[(A, B)] = of(Ty.TupleOf(List(a.ty, b.ty)), a, b)
  given [A, B, R](using a: LeanType[A], b: LeanType[B], r: LeanType[R]): LeanType[(A, B) => R] =
    of(Ty.FnOf(List(a.ty, b.ty), r.ty), a, b, r)
  // … sets, outcomes, tuples to three, functions of 0 to 6 inputs, `Flow[R]`, as today.
