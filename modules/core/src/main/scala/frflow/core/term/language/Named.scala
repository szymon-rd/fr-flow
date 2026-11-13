package frflow.core.term.language

import frflow.core.name.SymbolName
import frflow.core.term.language.Body
import frflow.core.ty.Ty

/** What a model names: a Declaration or Definition (applied with `app`), and a named
  * definition (printed once as a definition of the prover's and called by name, run by its body).
  */
trait Named[T[_]]:
  def param[A](name: SymbolName, ty: Ty): T[A]
  def define[F](d: Body[F]): T[F]
