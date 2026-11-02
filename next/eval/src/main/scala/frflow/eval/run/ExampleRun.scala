package frflow.eval.run

import frflow.core.analysis.Constrained
import frflow.core.example.{Example, Given}
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.NodeId
import frflow.core.Theory
import frflow.eval.{Env, Fn, Semantics}

/** An example checked against the code (owner §18): its fact evaluated with every Definition it mentions given its
  * meaning (`Wiring`: plain Scala, proven code run by the evaluator, a fixed value) and the values the example gives.
  * A value it gives code that breaks a rule on its type (`always[T]`, `Made`) is one code is never given, so the
  * example is refused (`BreaksRule`): its verdict would be about an input that cannot occur.
  */
final class ExampleRun(semantics: Semantics, t: Theory):
  def of(e: Example): OnCode =
    val at = env(e.givens)
    breaking(e, at).fold(Exprs.mentions(e.fact.value).symbols.filter(Constrained.isDeclaration(t, _)) match
      case Nil       => semantics.formula(e.fact)(at).fold(OnCode.NotEvaluated(_),
          v => if Fn.bool(v) then OnCode.Holds else OnCode.Fails)
      case abstracts => OnCode.Abstract(abstracts))(OnCode.BreaksRule(_))

  /** The first rule a value the fact gives code breaks: one an application is given (a value it only compares a
    * result with, `is`, is no input, and may be one no code makes: "a taken id is never added beside it").
    */
  private def breaking(e: Example, at: Env): Option[NodeId] =
    val inputs = Exprs.all(e.fact.value).flatMap {
      case Expr.Apply(_, args, _) => args
      case Expr.Call(_, args, _)  => args
      case _                      => Nil
    }
    val values = inputs.flatMap(Exprs.all).collect { case Expr.Lit(v, ty) => semantics.literal(v, ty) -> ty }
      .distinct
    Made.of(semantics, t).find(_.breaks(values.map(_._1), values.map(_._2), at)).map(_.always)

  private def env(gs: List[Given]): Env =
    val wiring = Wiring.onModels(semantics, t)
    Env.of(wiring.values(wiring.supplied(gs)))
