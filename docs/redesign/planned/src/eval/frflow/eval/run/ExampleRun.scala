package frflow.eval.run

import frflow.core.analysis.Constrained
import frflow.core.code.Values
import frflow.core.example.{Example, Given}
import frflow.core.expr.Exprs
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
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
    Env.of(Wiring(semantics, t).values(Values(gs.map(g => g.symbol -> value(g)).toMap)))

  private def value(g: Given): () => Any =
    val ty = t.vocabulary.symbol(g.symbol).map(_.ty).collect { case SymbolType.Typed(ty) => ty }.getOrElse(Ty.Unit)
    val held = semantics.literal(g.value, ty).unwrap
    () => held
