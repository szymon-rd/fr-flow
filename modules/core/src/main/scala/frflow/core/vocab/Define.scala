package frflow.core.vocab

import frflow.core.expr.Lambda
import frflow.core.name.DefName
import frflow.core.spec.Written

/** A named function of the domain (`val d = define { … }`): a Lean `def` printed once from its term, run as Scala by
  * its term's evaluation; its IR (`lambda`) for the analyses.
  */
final case class Define(name: DefName, written: Written[Lambda], form: DefineForm):
  def lambda: Lambda = written.value
