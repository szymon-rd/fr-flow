package frflow.cli.found

import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel
import frflow.dsl.node.Node
import frflow.dsl.term.TermSyntax.True

/** Classes of examples as a project's test classes may hold them, for `TestClasses`: one it makes, and one each way
  * it cannot (a constructor taking the model, a class nested in a class, a constructor that throws).
  */
object Found:
  lazy val kb: FrModel = FrModel("Found")(Node.claim("Holds.")(True))
  def broken: FrModel = throw IllegalStateException("no model here")

  class Made extends FrFlowExamples(kb):
    example("holds")(True)

  class Outer:
    class Inner extends FrFlowExamples(kb):
      example("holds")(True)
