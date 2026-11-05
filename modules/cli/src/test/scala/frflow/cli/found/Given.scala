package frflow.cli.found

import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel
import frflow.dsl.term.TermSyntax.True

/** A class of examples whose only constructor takes the model: a Scala default is no constructor without arguments. */
class Given(kb: FrModel = Found.kb) extends FrFlowExamples(kb):
  example("holds")(True)
