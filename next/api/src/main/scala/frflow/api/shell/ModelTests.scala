package frflow.api.shell

import frflow.api.Adapter
import frflow.core.Theory
import frflow.eval.Semantics
import frflow.project.program.ModelCheck

/** A store's implementation as the shell tests it: the model check, once the model is read. */
private[api] object ModelTests:
  def of[F[_]](a: Adapter[F], semantics: Semantics, t: Theory): Option[ModelCheck[F]] =
    ModelCheck.of[F, a.Boundary, a.State, a.Implementation](a.check, semantics, t)(using a.monad, a.refs)
