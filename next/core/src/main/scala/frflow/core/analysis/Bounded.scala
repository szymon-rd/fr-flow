package frflow.core.analysis

import frflow.core.Theory
import frflow.core.expr.{Expr, Exprs, Iteration, PrimOp, Quantifier}
import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** Scala's `Int` and `Long` wrap around and Lean's `Int` does not (`NumKind`): they compare but do not add (the DSL
  * has no arithmetic on them), and nothing may be said to exist of a type that holds one, since Lean could find one
  * Scala cannot hold. Said to exist: a `forall` or an `always` under a negation, on the left of `implies` or in a
  * condition (where it reads as an `∃`), and a Declaration (consistency asks Lean for a meaning of its type).
  */
object Bounded:
  def problems(t: Theory): List[Problem] = said(t) ++ declared(t)

  /** Whether a value of `ty` holds a Scala `Int` or `Long`, itself, as an element, or in a field. */
  def holds(t: Theory, ty: Ty): Boolean = holding(t, Set.empty)(ty)

  private def holding(t: Theory, seen: Set[TypeName])(ty: Ty): Boolean = Ty.parts(ty).exists {
    case Ty.Num(k)                => k.bounded
    case Ty.Data(n) if !seen(n)   => t.vocabulary.dataType(n).exists(_.fieldTypes.exists(holding(t, seen + n)))
    case _                        => false
  }

  private def said(t: Theory): List[Problem] = t.nodes.map(_.node).flatMap(n =>
    n.statement.said.toList.flatMap(f => existing(f.value, Polarity.Positive)).filter(holds(t, _)).distinct
      .map(Problem.SaidToExist(_, Problem.Place.Variable(n.id))))

  private def declared(t: Theory): List[Problem] = t.vocabulary.symbols.filter(s =>
    Constrained.isDeclaration(t, s.name)).flatMap(s => s.ty match
      case SymbolType.Typed(ty) if holds(t, ty) => List(Problem.SaidToExist(ty, Problem.Place.Value(s.name.value)))
      case _                                    => Nil)

  /** Where a formula is read as true (`Positive`), as false (`Negative`), or both ways. */
  private enum Polarity:
    case Positive, Negative, Both
    def flipped: Polarity = this match
      case Positive => Negative
      case Negative => Positive
      case Both     => Both

  /** The types of the variables `e` says exist, read at `p`. */
  private def existing(e: Expr, p: Polarity): List[Ty] = e match
    case Expr.Quant(q, xs, body)              =>
      val exists = q == Quantifier.Exists && p != Polarity.Negative || q != Quantifier.Exists && p != Polarity.Positive
      (if exists then xs.map(_.ty) else Nil) ++ existing(body, p)
    case Expr.Prim(PrimOp.Not, List(a), _)     => existing(a, p.flipped)
    case Expr.Prim(PrimOp.Implies, List(a, b), _) => existing(a, p.flipped) ++ existing(b, p)
    case Expr.Prim(PrimOp.And | PrimOp.Or, as, _) => as.flatMap(existing(_, p))
    case Expr.Iterate(how, over, _, body, _)  => existing(over, Polarity.Both) ++
        existing(body, if how == Iteration.Forall || how == Iteration.Exists then p else Polarity.Both)
    case Expr.Match(on, arms, _)              => existing(on, Polarity.Both) ++ arms.flatMap(a => existing(a.body, p))
    case Expr.Let(_, v, b)                    => existing(v, Polarity.Both) ++ existing(b, p)
    case Expr.Runs(r, w, _, _, _, post)       => existing(r, Polarity.Both) ++ existing(w, Polarity.Both) ++
        existing(post, p)
    case other                                => Exprs.children(other).flatMap(existing(_, Polarity.Both))
