package frflow.core.vocab

import frflow.core.expr.Lambda
import frflow.core.name.{DefName, SourceText}

/** A named function of the domain (`val d = define { … }`): a Lean `def`, run as Scala. */
final case class Define(name: DefName, lambda: Lambda, written: SourceText, form: DefineForm)
