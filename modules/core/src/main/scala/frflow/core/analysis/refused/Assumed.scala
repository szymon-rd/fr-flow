package frflow.core.analysis.refused

import frflow.core.analysis.{Constrained, Problem, Scope}
import frflow.core.Theory
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.core.spec.{NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.analysis.outside.{Guards, Reads}
import frflow.core.vocab.StateModel

/** The rules of an operation on a state known only by assumptions (G2, owner §36: "the assumed case"): what is
  * assumed of it is its whole meaning, so an assumption must say something of it (`Undefined` if none does); where a
  * rule is about its model's state, an assumption must say what its runs leave (`LeavesUnsaid`), or no program calling
  * it could be shown to keep the rule; and its model may not fail (`AssumedFailing`): a failing call's outcome is the
  * world's choice, which a run known only by assumptions does not take. Its runs are of its own model's state alone,
  * a function of it and of its inputs, so what is assumed of it reads no other model (`ReadsBeside`); and its results
  * are values from outside (owner §37), which a claim of `always` cannot cover (`AssumedMakes`).
  */
object Assumed:
  def problems(t: Theory): List[Problem] = t.vocabulary.models.flatMap(m => m.assumed.flatMap { sig =>
    val (op, about) = (sig.name, Constrained.assumptions(t, sig.name))
    val beside = about.flatMap(a => reads(t, a).filterNot(_ == m.name).map(Problem.ReadsBeside(a, op, _)))
    val made = claimed(t).collect { case (n, ty) if Guards.applies(t, ty, sig.result) => Problem.AssumedMakes(n, op) }
    (if m.fails.nonEmpty then List(Problem.AssumedFailing(op, m.name))
    else if about.isEmpty then Option.when(t.code.attached.contains(op))(Problem.Undefined(op)).toList
    else Option.when(ruled(t, m) && !about.exists(leaves(t, _, op)))(Problem.LeavesUnsaid(op, m.name)).toList) ++
      beside ++ made
  })

  /** The models a statement reads (`Reads`), and those of the operations it runs. */
  private def reads(t: Theory, id: NodeId): List[ModelName] =
    (Reads.models(t, id) ++ Constrained.of(t, id).flatMap(t.vocabulary.modelOf).map(_.name)).distinct

  /** The claims of `always[T]`, each with its `T`. */
  private def claimed(t: Theory): List[(NodeId, Ty)] = t.nodes.map(_.node)
    .filter(_.statement.kind == NodeKind.Claim).flatMap(n => n.statement.range.collect { case Range.Made(ty) =>
      n.id -> ty })

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
