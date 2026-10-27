package frflow.proof.lean.term

import frflow.core.name.SymbolName
import frflow.proof.lean.ast.{LExpr, LOp, LeanName, Names}
import frflow.proof.lean.lower.{Atoms, LowerEnv}

/** The arms a run's outcome is matched with (`Worlds.runs`, `Worlds.fails`): a run's pair taken apart, `| (result,
  * after) => post`; of a program that may fail, `| (Except.ok result, after) => post | _ => True` for the runs that
  * succeed and `| (Except.error e, after) => post | _ => True` for those that fail. A run is of a program that may
  * fail when what it applies is one, or what stands for one (`standing`: its code, in a witness or an `impl`).
  */
final class Outcomes(env: LowerEnv, standing: Map[SymbolName, LExpr]):
  import Atoms.{const, name}

  private val failing: Set[LExpr] =
    env.failing.keySet.map(n => Outcomes.head(standing.getOrElse(n, LExpr.Name(Names.ident(n.value)))))

  def succeeded(run: LExpr, r: LeanName, w: LeanName, post: LExpr): List[(LExpr, LExpr)] =
    if !failing(Outcomes.head(run)) then List(LExpr.Tuple(List(LExpr.Name(r), LExpr.Name(w))) -> post)
    else List(LExpr.Tuple(List(LExpr.App(const("Except.ok"), List(LExpr.Name(r))), LExpr.Name(w))) -> post,
      name("_") -> name("True"))

  def failed(e: LeanName, w: LeanName, post: LExpr): List[(LExpr, LExpr)] =
    List(LExpr.Tuple(List(LExpr.App(const("Except.error"), List(LExpr.Name(e))), LExpr.Name(w))) -> post,
      name("_") -> name("True"))

object Outcomes:
  /** `((after.Shelf = before.Shelf) ∧ …)`: one equation per model's field of the world, `True` with none; the faults
    * are no model's (`Worlds.unchanged`).
    */
  def unchanged(env: LowerEnv, after: LExpr, before: LExpr): LExpr =
    env.models.map(f => LExpr.Paren(LExpr.Infix(LOp.Eq, LExpr.Dot(after, f.text), LExpr.Dot(before, f.text))))
      match
        case Nil        => Atoms.name("True")
        case one :: Nil => one
        case each       => LExpr.Paren(each.reduceRight(LExpr.Infix(LOp.And, _, _)))

  /** What a term applies, through its parentheses: `book` of `(book request before)`. */
  def head(e: LExpr): LExpr = e match
    case LExpr.Paren(inner) => head(inner)
    case LExpr.App(f, _)    => head(f)
    case other              => other
