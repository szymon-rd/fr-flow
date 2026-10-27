package frflow.core.term.algebra

import frflow.core.name.SymbolName
import frflow.core.term.Body
import frflow.core.ty.Ty

/** What a model names: a Declaration or Definition (applied with `app`), and a named
  * definition (printed once as a Lean `def` and called by name, run by its body).
  */
trait Named[T[_]]:
  def param[A](name: SymbolName, ty: Ty): T[A]
  def define[F](d: Body[F]): T[F]
