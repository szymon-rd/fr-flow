package frflow.dsl.shape

import frflow.core.name.DefName
import frflow.dsl.build.{Site, Source}
import frflow.dsl.term.Def

/** `define { (a: Term[A], …) => body }`: a define named as its val, its body built when elaborated. */
object Defines:
  inline def define[F](using b: DefineShape[F])(inline body: b.Lam): Def[F] =
    val name = DefName(Source.valName)
    Def(name, Elab.lambda(Site.Define(name), b.types)(b.call(body, _), Source.of(body)))
