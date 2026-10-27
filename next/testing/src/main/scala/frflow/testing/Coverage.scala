package frflow.testing

import frflow.core.expr.Lambda
import frflow.core.name.NodeId
import frflow.core.spec.{CallForms, Form, Written}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.eval.{Env, EvalError, Semantics}
import frflow.eval.run.Wiring
import frflow.eval.term.Run
import frflow.testing.report.{Hits, Target}
import scala.collection.mutable.ListBuffer
import scala.util.Try

/** What of a claim a case reaches, as today's tests count it: each implication's premise holding, each side of an
  * or, each condition both ways, each arm of a match (an option's and an either's fold among them), each list or
  * option a quantifier ranges over not empty (`Watching`). The claim is read whole, at the case's variables, every
  * Definition given its meaning; counted only when the case gives every variable it binds (`counted`).
  */
final class Coverage(semantics: Semantics, t: Theory, node: NodeId, inputs: List[Ty]):
  private val wiring = Wiring.onModels(semantics, t)
  private val claim: Option[Written[Lambda]] = t.node(node).flatMap(_.statement.said).map(CallForms.whole)
    .filter(_.value.params.map(_.ty) == inputs)

  /** Every target of the claim, each at zero. */
  val zero: Hits =
    val seen = ListBuffer.empty[Target]
    claim.foreach(w => built(w, Watching(seen += _, _ => (), surveying = true)))
    Hits.zero(seen.distinct.toList)

  /** Each target the case reached, once. */
  def of(c: Case): Hits = claim.fold(Hits(Map.empty)) { w =>
    val reached = ListBuffer.empty[Target]
    val run = built(w, Watching(_ => (), reached += _, surveying = false))
    val env = w.value.params.zip(c.inputs.zip(inputs).map(semantics.literal))
      .foldLeft(Env.of(wiring.values(wiring.supplied(c.givens))))((e, xv) => e.bind(xv._1.id, xv._2))
    val _ = Try(run(env))
    Hits(reached.distinct.map(_ -> 1).toMap)
  }

  private def built(w: Written[Lambda], watching: Watching): Run[Any] = w.form match
    case Form.Term(s)  =>
      val run = s.run[Run](watching)
      env => run(env)
    case Form.Steps(_) => _ => Left(EvalError.Steps)
