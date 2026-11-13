package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.term.Selector
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.build.Declarations
import scala.annotation.implicitNotFound

/** What a Scala type is in the IR, the domain types it needs declared, and, for a record, its fields: each a
  * selector with the field's own `RocqType`.
  */
@implicitNotFound("FrFlow: ${A} is not a domain type yet: add `derives RocqType` to its declaration " +
  "(`final case class … derives RocqType`, `enum … derives RocqType`)")
trait RocqType[A]:
  def ty: Ty
  def declares: Declarations
  def fields: List[RocqType.Field[A, ?]] = Nil
  /** Of a Scala type with no `RocqType` (a code-only Definition's), that type's name: no statement speaks of it. */
  def codeOnly: Option[String] = None

object RocqType:
  /** A record's field: its selector, typed by the field's `RocqType`. */
  final case class Field[R, F](selector: Selector[R, F], rocqType: RocqType[F])

  def apply[A](using t: RocqType[A]): RocqType[A] = t
  def of[A](t: Ty, parts: RocqType[?]*): RocqType[A] = new RocqType[A]:
    val ty: Ty = t
    val declares: Declarations = parts.toList.foldMap(_.declares)

  given RocqType[Boolean] = of(Ty.Bool)
  given RocqType[String] = of(Ty.Str)
  given RocqType[Unit] = of(Ty.Unit)
  given RocqType[Int] = of(Ty.Num(NumKind.Int32))
  given RocqType[Long] = of(Ty.Num(NumKind.Int64))
  given RocqType[BigInt] = of(Ty.Num(NumKind.Big))
  given [A](using a: RocqType[A]): RocqType[List[A]] = of(Ty.ListOf(a.ty), a)
  given option[A](using a: RocqType[A]): RocqType[Option[A]] = of(Ty.OptionOf(a.ty), a)
  given either[A, B](using a: RocqType[A], b: RocqType[B]): RocqType[Either[A, B]] = of(Ty.EitherOf(a.ty, b.ty), a, b)

  given [K, V](using k: RocqType[K], v: RocqType[V]): RocqType[Map[K, V]] = of(Ty.MapOf(k.ty, v.ty), k, v)
  /** A pair's: its two sides its fields (`p._1`, `p._2`), each typed by its own `RocqType`. */
  given [A, B](using a: RocqType[A], b: RocqType[B]): RocqType[(A, B)] = new RocqType[(A, B)]:
    val ty: Ty = Ty.TupleOf(List(a.ty, b.ty))
    val declares: Declarations = a.declares |+| b.declares
    override val fields: List[Field[(A, B), ?]] =
      List(Field(Selector.first[A, B](a.ty), a), Field(Selector.second[A, B](b.ty), b))
  /** A case class's or an enum's, derived once where it is declared (`enum Request derives RocqType`: the given in its
    * companion, which every use finds), by `DataMacros`. Not an inline given: one re-derived at every use expands a
    * type's whole structure into each, and sharing's largest file then passed the JVM's limits on a method's and a
    * class's size (`r43-spike/`).
    */
  inline def derived[T](using scala.deriving.Mirror.Of[T]): RocqType[T] = ${ DataMacros.derived[T] }
  given fn[A, B](using a: RocqType[A], b: RocqType[B]): RocqType[A => B] = of(Ty.FnOf(List(a.ty), b.ty), a, b)
  given [A, B, R](using a: RocqType[A], b: RocqType[B], r: RocqType[R]): RocqType[(A, B) => R] =
    of(Ty.FnOf(List(a.ty, b.ty), r.ty), a, b, r)
  given [A, B, C, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], r: RocqType[R]): RocqType[(A, B, C) => R] =
    of(Ty.FnOf(List(a.ty, b.ty, c.ty), r.ty), a, b, c, r)
  given [A, B, C, D, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], d: RocqType[D], r: RocqType[R])
      : RocqType[(A, B, C, D) => R] = of(Ty.FnOf(List(a.ty, b.ty, c.ty, d.ty), r.ty), a, b, c, d, r)
  given [A, B, C, D, E, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], d: RocqType[D], e: RocqType[E],
      r: RocqType[R]): RocqType[(A, B, C, D, E) => R] =
    of(Ty.FnOf(List(a.ty, b.ty, c.ty, d.ty, e.ty), r.ty), a, b, c, d, e, r)
  given [A, B, C, D, E, G, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], d: RocqType[D], e: RocqType[E],
      g: RocqType[G], r: RocqType[R]): RocqType[(A, B, C, D, E, G) => R] =
    of(Ty.FnOf(List(a.ty, b.ty, c.ty, d.ty, e.ty, g.ty), r.ty), a, b, c, d, e, g, r)
  given [A](using a: RocqType[A]): RocqType[Set[A]] = of(Ty.SetOf(a.ty), a)
  given [A, B, C](using a: RocqType[A], b: RocqType[B], c: RocqType[C]): RocqType[(A, B, C)] =
    of(Ty.TupleOf(List(a.ty, b.ty, c.ty)), a, b, c)
