package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.term.{Program, Selector, World}
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.build.Declarations
import scala.annotation.implicitNotFound

/** What a Scala type is in the IR, the domain types it needs declared, and, for a record, its fields: each a
  * selector with the field's own `LeanType`.
  */
@implicitNotFound("${A} is not a domain type yet: add `derives LeanType` to its declaration " +
  "(`final case class … derives LeanType`, `enum … derives LeanType`)")
trait LeanType[A]:
  def ty: Ty
  def declares: Declarations
  def fields: List[LeanType.Field[A, ?]] = Nil

object LeanType:
  /** A record's field: its selector, typed by the field's `LeanType`. */
  final case class Field[R, F](selector: Selector[R, F], leanType: LeanType[F])

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
  given LeanType[World] = of(Ty.World)
  given [A](using a: LeanType[A]): LeanType[List[A]] = of(Ty.ListOf(a.ty), a)
  given option[A](using a: LeanType[A]): LeanType[Option[A]] = of(Ty.OptionOf(a.ty), a)
  given either[A, B](using a: LeanType[A], b: LeanType[B]): LeanType[Either[A, B]] = of(Ty.EitherOf(a.ty, b.ty), a, b)
  given [R](using r: LeanType[R]): LeanType[Program[R]] = of(Ty.FlowOf(r.ty), r)
  given [K, V](using k: LeanType[K], v: LeanType[V]): LeanType[Map[K, V]] = of(Ty.MapOf(k.ty, v.ty), k, v)
  given [A, B](using a: LeanType[A], b: LeanType[B]): LeanType[(A, B)] = of(Ty.TupleOf(List(a.ty, b.ty)), a, b)
  /** A case class's or an enum's, derived once where it is declared (`enum Request derives LeanType`: the given in its
    * companion, which every use finds), by `DataMacros`. Not an inline given: one re-derived at every use expands a
    * type's whole structure into each, and sharing's largest file then passed the JVM's limits on a method's and a
    * class's size (`r43-spike/`).
    */
  inline def derived[T](using scala.deriving.Mirror.Of[T]): LeanType[T] = ${ DataMacros.derived[T] }
  given fn[A, B](using a: LeanType[A], b: LeanType[B]): LeanType[A => B] = of(Ty.FnOf(List(a.ty), b.ty), a, b)
  given [A, B, R](using a: LeanType[A], b: LeanType[B], r: LeanType[R]): LeanType[(A, B) => R] =
    of(Ty.FnOf(List(a.ty, b.ty), r.ty), a, b, r)
  given [A, B, C, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], r: LeanType[R]): LeanType[(A, B, C) => R] =
    of(Ty.FnOf(List(a.ty, b.ty, c.ty), r.ty), a, b, c, r)
  given [A, B, C, D, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], r: LeanType[R])
      : LeanType[(A, B, C, D) => R] = of(Ty.FnOf(List(a.ty, b.ty, c.ty, d.ty), r.ty), a, b, c, d, r)
  // … sets, outcomes, tuples to three, functions of 0 to 6 inputs, as today.
