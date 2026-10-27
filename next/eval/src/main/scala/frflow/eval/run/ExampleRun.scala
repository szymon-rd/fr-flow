package frflow.eval.run

import frflow.core.analysis.Constrained
import frflow.core.example.{Example, Given}
import frflow.core.expr.Exprs
import frflow.core.Theory
import frflow.eval.{Env, Fn, Semantics}

/** An example checked against the code (owner §18): its fact evaluated with every Definition it mentions given its
  * meaning (`Wiring`: plain Scala, proven code run by the evaluator, a fixed value) and the values the example gives.
  */
final class ExampleRun(semantics: Semantics, t: Theory):
  def of(e: Example): OnCode =
    Exprs.mentions(e.fact.value).symbols.filter(Constrained.isDeclaration(t, _)) match
      case Nil       => semantics.formula(e.fact)(env(e.givens)).fold(OnCode.NotEvaluated(_),
          v => if Fn.bool(v) then OnCode.Holds else OnCode.Fails)
      case abstracts => OnCode.Abstract(abstracts)

  private def env(gs: List[Given]): Env =
    val wiring = Wiring(semantics, t)
    Env.of(wiring.values(wiring.supplied(gs)))
