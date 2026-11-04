package frflow.proof.lean.term

import cats.syntax.all.*
import frflow.core.name.DefName
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Atoms, LowerType, Naming}

/** A schedule's freezing try (`Prop.Frozen`) as Lean: `∀ s₀ s₁ …, init₀ s₀ → init₁ s₁ → … → ∀ (d : Int), 0 < d →
  * ¬ rule (s₀ + d) s₁ …`, the clock's state first, each other model's after, each `initially` and the rule on their
  * open terms bound first (`overOpens`), each a define on its open terms (`opened`).
  */
final class FrozenTry(naming: Naming, opened: DefName => LExpr, overOpens: (List[DefName], LExpr) => LExpr):
  def apply(rule: DefName, starts: List[(Option[DefName], Ty)]): LExpr =
    val names = (starts.indices.toList.map(i => s"s$i") :+ "d").traverse(n => Naming.helper(n, Set.empty))
      .runA(naming).value
    val (ss, d) = (names.init, names.last)
    val hyps = starts.zip(ss).flatMap((st, s) => st._1.map(i => Atoms.call(opened(i), List(LExpr.Name(s)))))
    val moved = LExpr.Paren(LExpr.Infix(LOp.Add, LExpr.Name(ss.head), LExpr.Name(d)))
    val stays = LExpr.Forall(List(LBinder.Explicit(d, Atoms.name("Int"))), LExpr.Infix(LOp.Arrow,
      LExpr.Infix(LOp.Lt, Atoms.name("0"), LExpr.Name(d)),
      LExpr.Prefix(LPrefix.NotSpaced, Atoms.call(opened(rule), moved :: ss.tail.map(LExpr.Name(_))))))
    val binders = ss.zip(starts).map((s, st) => LBinder.Explicit(s, LowerType(st._2)))
    overOpens(rule :: starts.flatMap(_._1), LExpr.Forall(binders, (hyps :+ stays).reduceRight(LExpr.Infix(LOp.Arrow,
      _, _))))
