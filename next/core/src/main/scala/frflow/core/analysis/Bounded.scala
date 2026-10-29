package frflow.core.analysis

import frflow.core.Theory
import frflow.core.code.Code
import frflow.core.spec.Range
import frflow.core.expr.{Expr, Exprs, Iteration, PrimOp, Quantifier}
import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** Scala's `Int` and `Long` wrap around and Lean's `Int` does not (`NumKind`): they compare but do not add (the DSL
  * has no arithmetic on them), and nothing may be said to exist of a type that holds one, since Lean could find one
  * Scala cannot hold. Said to exist, by the statement or by what FrFlow asks of it: a `forall` or an `always` under a
  * negation, on the left of `implies` or in a condition (where it reads as an `∃`), one over a condition
  * (`satisfiable_` asks that it can hold), a rule of `always` (`inhabited_` asks a value meeting it, and of a store's
  * state one it starts in), a Declaration, and a Definition Lean has no meaning for (plain Scala, known by its
  * statements: consistency asks Lean for a meaning of its type).
  */
object Bounded:
  def problems(t: Theory): List[Problem] = (said(t) ++ rules(t) ++ declared(t)).distinct

  /** Whether a value of `ty` holds a Scala `Int` or `Long`, itself, as an element, or in a field. */
  def holds(t: Theory, ty: Ty): Boolean = holding(t, Set.empty)(ty)

  private def holding(t: Theory, seen: Set[TypeName])(ty: Ty): Boolean = Ty.parts(ty).exists {
    case Ty.Num(k)                => k.bounded
    case Ty.Data(n) if !seen(n)   => t.vocabulary.dataType(n).exists(_.fieldTypes.exists(holding(t, seen + n)))
    case _                        => false
  }

  /** What a statement says exists, in its formula and in the defines it calls, however far (read both ways: a define's
    * body may stand anywhere).
    */
  private def said(t: Theory): List[Problem] = t.nodes.map(_.node).flatMap(n => n.statement.said.toList.flatMap(f =>
    existing(f.value, Polarity.Positive) ++ t.vocabulary.closure(Exprs.mentions(f.value).defines)
      .flatMap(d => existing(d.lambda.body, Polarity.Both))).filter(holds(t, _)).distinct
    .map(Problem.SaidToExist(_, Problem.Place.Variable(n.id))))

  /** Each rule of `always[T]` over a `T` holding one, and of `always(stored)` over a state holding one. */
  private def rules(t: Theory): List[Problem] = t.nodes.map(_.node).flatMap(n => n.statement.range.toList.flatMap {
    case Range.Made(ty) if holds(t, ty) => List(Problem.SaidToExist(ty, Problem.Place.Variable(n.id)))
    case Range.Reached(ms)              => ms.flatMap(t.vocabulary.model).filter(m => holds(t, m.state))
        .map(m => Problem.SaidToExist(m.state, Problem.Place.State(m.name)))
    case _                              => Nil
  })

  /** A Declaration, or a Definition given plain Scala (Lean is given no meaning of it), of a type holding one. */
  private def declared(t: Theory): List[Problem] = t.vocabulary.symbols.filter(s =>
    Constrained.isDeclaration(t, s.name) || t.code.attached.get(s.name).exists(_.code match
      case Code.Tested(_, _) => true
      case _                 => false)).flatMap(s => s.ty match
      case SymbolType.Typed(ty) if holds(t, ty) => List(Problem.SaidToExist(ty, Problem.Place.Value(s.name.value)))
      case _                                    => Nil)

  /** A body with a condition (`a implies b`): what `satisfiable_` asks can hold, over the variables around it. */
  private def conditional(body: Expr): Boolean = Exprs.all(body).exists {
    case Expr.Prim(PrimOp.Implies, _, _) => true
    case _                               => false
  }

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
      val exists = q == Quantifier.Exists && p != Polarity.Negative || q != Quantifier.Exists &&
        (p != Polarity.Positive || conditional(body))
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
