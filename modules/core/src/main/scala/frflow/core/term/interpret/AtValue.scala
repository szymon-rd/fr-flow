package frflow.core.term.interpret

import frflow.core.term.{Annotation, Bound, Final, Sym}

/** A formula's leading `always` at a value: `always(x)(p)` at `v` is `p(v)`, what the rule says of `v` (the
  * hypothesis a variable comes with, `Guards`; the rule of the world a run ends in, `Keeping`). A context-passing
  * interpreter, as `Opened` is: the context is the value still to put in, which every other operation drops.
  */
final class AtValue[T[_]](s: Sym[T]) extends Forward[T, [a] =>> Option[T[Any]] => T[a]]:
  private type V[A] = Option[T[Any]] => T[A]
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): V[A] = _ => t
  protected def bwd[A](u: V[A]): T[A] = u(None)

  override def noted[A](n: Annotation, t: V[A]): V[A] = v => s.noted(n, t(v))

  override def always[A](x: Bound[A])(p: V[A] => V[Boolean]): V[Boolean] = {
    case Some(v) => p(_ => v.asInstanceOf[T[A]])(None) // a value of the binder's type: `Guards` matched its `Ty`
    case None    => super.always(x)(p)(None)
  }

object AtValue:
  def of[T[_], A](rule: Final[Boolean], s: Sym[T], v: T[A]): T[Boolean] =
    rule[[a] =>> Option[T[Any]] => T[a]](AtValue(s))(Some(v.asInstanceOf[T[Any]]))
