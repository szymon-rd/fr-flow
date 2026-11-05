package frflow.cli.found

import frflow.dsl.example.FrFlowExamples
import frflow.dsl.term.TermSyntax.True

/** A class of examples whose constructor throws: its model cannot be built. */
class Throwing extends FrFlowExamples(Found.broken):
  example("holds")(True)
