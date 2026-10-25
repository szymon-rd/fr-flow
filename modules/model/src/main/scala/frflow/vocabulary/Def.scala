package frflow
package vocabulary

import frflow.program.Lambdas
import frflow.protocol.Walk

/** A function of the domain, defined once with terms: a Lean definition named as its `val`, and run as Scala. */
final class Def[F] @scala.annotation.publicInBinary private[frflow] (val lifted: Lifted[F], private[frflow] val resultType: LeanType[?],
    named: Option[String] = None, val isFlow: Boolean = false):
  lazy val name: String = named.orElse(Lambdas.valName(this, lifted.fn.nn))
    .getOrElse(throw IllegalStateException("FrFlow: a `define` must be assigned to a top-level val, or a val of an object"))
  def fn: F = lifted.value
  override def toString: String = name

object Def:
  def closure(ds: Iterable[Def[?]]): List[Def[?]] = Walk.preorder(ds.toList, _.name)(_.lifted.defs)

  /** `define { (b: Term[Book]) => b.pages >= 100 }`: named in Lean as the val it is assigned to. */
  inline def define[R](inline f: () => Term[R])(using r: LeanType[R]): Def[() => R] =
    Def(Lifted.lambda(f, Nil, Source.text(f)), r)
  inline def define[A, R](inline f: Term[A] => Term[R])(using a: LeanType[A], r: LeanType[R]): Def[A => R] =
    Def(Lifted.lambda(f, List(a), Source.text(f)), r)
  inline def define[A, B, R](inline f: (Term[A], Term[B]) => Term[R])(using a: LeanType[A], b: LeanType[B], r: LeanType[R]): Def[(A, B) => R] =
    Def(Lifted.lambda(f, List(a, b), Source.text(f)), r)
  inline def define[A, B, C, R](inline f: (Term[A], Term[B], Term[C]) => Term[R])(using a: LeanType[A], b: LeanType[B], c: LeanType[C],
      r: LeanType[R]): Def[(A, B, C) => R] =
    Def(Lifted.lambda(f, List(a, b, c), Source.text(f)), r)
  inline def define[A, B, C, D, R](inline f: (Term[A], Term[B], Term[C], Term[D]) => Term[R])(using a: LeanType[A], b: LeanType[B],
      c: LeanType[C], d: LeanType[D], r: LeanType[R]): Def[(A, B, C, D) => R] =
    Def(Lifted.lambda(f, List(a, b, c, d), Source.text(f)), r)
  inline def define[A, B, C, D, E, R](inline f: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[R])(using a: LeanType[A], b: LeanType[B],
      c: LeanType[C], d: LeanType[D], e: LeanType[E], r: LeanType[R]): Def[(A, B, C, D, E) => R] =
    Def(Lifted.lambda(f, List(a, b, c, d, e), Source.text(f)), r)
  inline def define[A, B, C, D, E, F, R](inline f: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[F]) => Term[R])(using a: LeanType[A],
      b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], g: LeanType[F], r: LeanType[R]): Def[(A, B, C, D, E, F) => R] =
    Def(Lifted.lambda(f, List(a, b, c, d, e, g), Source.text(f)), r)
