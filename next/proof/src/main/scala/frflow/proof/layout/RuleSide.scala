package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.analysis.outside.Guards
import frflow.core.expr.{Expr, Exprs, Quantifier}
import frflow.core.name.DefName
import frflow.core.spec.{Form, Range}
import frflow.core.ty.Ty
import frflow.core.vocab.Define

/** The defines a rule (`always`) calls, through the defines it calls (the second 13b re-review, RB1). A rule holds of
  * values with no guard of its own: what it calls is printed as written, unguarded, or a rule would be about itself.
  * A statement takes every rule as a hypothesis on what it quantifies over (`Guarded`), so where it calls such a
  * define whose quantifiers a value rule guards (or one calling such a define), it calls a second `def` of it, its
  * `forall`s guarded as the statement's own (`<d>_guarded`): a define read inline means what it does named, whoever
  * calls it.
  */
final case class RuleSide(defines: Set[DefName], twice: Set[DefName])

object RuleSide:
  def of(r: Resolved): RuleSide =
    val t = r.theory
    val v = t.vocabulary
    val rules = Guards.byAlways(t).map((n, _) => DefName(n.value)).toSet
    val side = v.closure(rules.toList).map(_.name).toSet
    val made = t.nodes.flatMap(_.node.statement.range).collect { case Range.Made(u) if u != Ty.World => u }
    def guarded(d: Define) = d.written.form match
      case Form.Term(_) => Exprs.all(d.lambda.body).exists {
          case Expr.Quant(Quantifier.Forall | Quantifier.Exists, xs, _) =>
            xs.exists(x => made.exists(Guards.applies(t, _, x.ty)))
          case _                                                         => false
        }
      case Form.Steps(_) => false
    val candidates = (side -- rules).toList.flatMap(v.define)
    def grow(twice: Set[DefName]): Set[DefName] =
      val more = twice ++ candidates.filter(d => Exprs.mentions(d.lambda.body).defines.exists(twice)).map(_.name)
      if more == twice then twice else grow(more)
    RuleSide(side, grow(candidates.filter(guarded).map(_.name).toSet))

