package frflow.core.term.interpret

import frflow.core.expr.Binder
import frflow.core.term.{Annotation, Bound, Ext, Sym}
import frflow.core.ty.Ty

/** A value with the side of an `Either` it was made on, where known. */
final case class Known[T[_], A](t: T[A], side: Option[Either[T[Any], T[Any]]])

/** `Substituted`, and each of `sides`' variables an `Either` known to be its `Left` or `Right` (a failing run's
  * outcome, `node.Closing`): a `fold` of a value made on a known side is that side's branch, so a run read as failing
  * states each side's post as written, not a `fold` of a constructor (`match (Except.ok r) with …`).
  */
final class Sided[T[_]](protected val base: Sym[T], env: Map[Binder, T[Any]],
    sides: Map[Binder, Either[T[Any], T[Any]]]) extends Forward[T, [a] =>> Known[T, a]]:
  private type K[A] = Known[T, A]
  protected def fwd[A](t: T[A]): K[A] = Known(t, None)
  protected def bwd[A](u: K[A]): T[A] = u.t

  override def free[A](x: Binder): K[A] = sides.get(x) match
    case Some(side) => Known(made(side, x.ty).asInstanceOf[T[A]], Some(side)) // an outcome, of `x`'s type
    case None       => fwd(env.get(x).fold(base.free[A](x))(_.asInstanceOf[T[A]]))
  override def left[E, A](e: K[E], ty: Ty): K[Either[E, A]] =
    Known(base.left(e.t, ty), Some(Left(e.t.asInstanceOf[T[Any]])))
  override def right[E, A](a: K[A], ty: Ty): K[Either[E, A]] =
    Known(base.right(a.t, ty), Some(Right(a.t.asInstanceOf[T[Any]])))
  override def foldEither[E, A, R](v: K[Either[E, A]], e: Bound[E], a: Bound[A])(l: K[E] => K[R], r: K[A] => K[R])
      : K[R] = v.side match
    case Some(Left(x))  => l(fwd(x.asInstanceOf[T[E]]))
    case Some(Right(x)) => r(fwd(x.asInstanceOf[T[A]]))
    case None           => super.foldEither(v, e, a)(l, r)
  override def noted[A](n: Annotation, t: K[A]): K[A] = Known(base.noted(n, t.t), t.side)
  override def extension[E[_[_]]](key: Ext[E]): Option[E[[a] =>> Known[T, a]]] = None

  private def made(side: Either[T[Any], T[Any]], ty: Ty): T[Any] = side.fold(base.left[Any, Any](_, ty),
    base.right[Any, Any](_, ty)).asInstanceOf[T[Any]]
