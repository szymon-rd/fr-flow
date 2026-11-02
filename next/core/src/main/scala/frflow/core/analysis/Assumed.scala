package frflow.core.analysis

import frflow.core.Theory
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{NodeKind, Range}
import frflow.core.vocab.StateModel

/** The rules of an operation on a state known only by assumptions (G2, owner §36: "the assumed case"): what is
  * assumed of it is its whole meaning, so an assumption must say something of it (`Undefined` if none does); where a
  * rule is about its model's state, an assumption must say what its runs leave (`LeavesUnsaid`), or no program calling
  * it could be shown to keep the rule; and its model may not fail (`AssumedFailing`): a failing call's outcome is the
  * world's choice, which a run known only by assumptions does not take.
  */
object Assumed:
  def problems(t: Theory): List[Problem] = t.vocabulary.models.flatMap(m => m.assumed.map(_.name).flatMap { op =>
    val about = Constrained.statements(t, op).filter(id => t.node(id).exists(_.statement.kind == NodeKind.Assumption))
    if m.fails.nonEmpty then List(Problem.AssumedFailing(op, m.name))
    else if about.isEmpty then Option.when(t.code.attached.contains(op))(Problem.Undefined(op)).toList
    else Option.when(ruled(t, m) && !about.exists(leaves(t, _, op)))(Problem.LeavesUnsaid(op, m.name)).toList
  })

  /** Whether a rule is about the model's state: an `always(stored)` of it, or an `always[T]` of a type it holds. */
  private def ruled(t: Theory, m: StateModel): Boolean = t.nodes.map(_.node).exists(n =>
    n.statement.range.exists {
      case r @ (Range.Made(_) | Range.Reached(_)) => Scope.models(t, r).exists(_.name == m.name)
      case Range.Possible                        => false
    })

  /** Whether the assumption reads the world a run of `op` leaves. */
  private def leaves(t: Theory, id: NodeId, op: SymbolName): Boolean =
    t.node(id).toList.flatMap(_.statement.exprs).flatMap(Exprs.all).exists {
      case Expr.Runs(run, _, _, _, after, post) if applies(run, op) =>
        Exprs.all(post).exists {
          case Expr.Var(x) => x == after
          case _           => false
        }
      case _                                                        => false
    }

  private def applies(run: Expr, op: SymbolName): Boolean = run match
    case Expr.Sym(s, _)                   => s == op
    case Expr.Apply(Expr.Sym(s, _), _, _) => s == op
    case _                                => false
