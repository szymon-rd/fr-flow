package frflow.core.term.interpret

import frflow.core.name.SymbolName
import frflow.core.term.{Ext, Final, Sym}
import frflow.core.ty.Ty

/** Each symbol at the type `types` gives it, every other operation as `base` has it: a term written before what its
  * symbols are was known (a program's error, read off its code: `Failing.typed`) at their types now.
  */
final class Retyped[T[_]](protected val base: Sym[T], types: SymbolName => Option[Ty]) extends Forward[T, T]:
  protected def fwd[A](t: T[A]): T[A] = t
  protected def bwd[A](u: T[A]): T[A] = u
  override def param[A](name: SymbolName, ty: Ty): T[A] = base.param(name, types(name).getOrElse(ty))
  override def extension[E[_[_]]](key: Ext[E]): Option[E[T]] = base.extension(key)

object Retyped:
  def of[A](t: Final[A], types: SymbolName => Option[Ty]): Final[A] = [T[_]] => (s: Sym[T]) => t(Retyped(s, types))
