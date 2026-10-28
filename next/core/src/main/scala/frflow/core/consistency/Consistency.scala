package frflow.core.consistency

import frflow.core.analysis.{Callees, Constrained, Scope}
import frflow.core.analysis.Outsides
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, OutsideFact}
import frflow.core.name.{NodeId, SourceText, SymbolName}
import frflow.core.spec.{NodeKind, Range, Written}
import frflow.core.term.interpret.ToExpr
import frflow.core.Theory

/** The consistency and vacuity obligations of a theory (owner §15, §18), derived from it alone: no example is read.
  * The bottom statements and the premises beside them, split into groups that share open values, each with the
  * witnesses derived for it; each `always(stored)` with the state the store starts in; each `always[T]` and each
  * claim's condition, to be shown possible.
  */
object Consistency:
  def of(t: Theory): List[Group] = sharing(t) ++ starts(t)

  /** `inhabited_` of every `always[T]`, claimed or assumed, and `satisfiable_` of every claim's condition. */
  def vacuity(t: Theory): List[Vacuity] = t.nodes.map(_.node).flatMap(n => n.statement.range.toList.flatMap {
    case Range.Made(ty)                                       => List(Vacuity.Inhabited(n.id, ty))
    case Range.Possible if n.statement.kind == NodeKind.Claim =>
      n.statement.said.toList.flatMap(f => Conditions.of(f.term, ToExpr).zipWithIndex.map((c, i) =>
        Vacuity.Satisfiable(n.id, i, c.over.map(_.ty))))
    case _                                                   => Nil
  })

  /** The statements no proven step gives: Lean states them, about every possible value, with no parts. The claims
    * among them and the assumptions beside them (an outside system's promise) are the bottom of the theory.
    */
  def bottom(t: Theory): List[NodeId] = t.nodes.map(_.node).collect {
    case n if n.statement.stated && n.statement.range.contains(Range.Possible) &&
        t.refinement.parts(n.id).isEmpty => n.id
  }

  /** What a statement leaves open: the Declarations it mentions, and the Definitions no proof or fixed value gives
    * a meaning (plain Scala, tested; or none), its own and those the proven code standing in it leaves open
    * (`bookedAfterIsStored` mentions `book`, whose program calls `granted`).
    */
  def open(t: Theory, id: NodeId): List[SymbolName] =
    (Constrained.of(t, id) ++ Callees.of(t, id).toList.flatMap(_.calls.symbols)).distinct.filter(isOpen(t, _))

  /** What a proven Definition's code leaves open; nothing of any other. */
  def reach(t: Theory, s: SymbolName): List[SymbolName] =
    Callees.ofDefinition(t, s).toList.flatMap(_.calls.symbols).filter(isOpen(t, _))

  private def isOpen(t: Theory, s: SymbolName): Boolean = t.vocabulary.symbol(s).nonEmpty &&
    (Constrained.isDeclaration(t, s) || t.code.attached.get(s).forall(a => a.code.proven.isEmpty && !fixed(a.code)))

  /** What a statement takes for every value code is given: the Definitions provided where the code runs. */
  def provided(t: Theory, id: NodeId): List[SymbolName] =
    Constrained.of(t, id).filter(s => t.code.attached.get(s).exists(_.code == Code.Provided))

  private def fixed(c: Code): Boolean = c match
    case Code.Valued(_) | Code.Provided => true
    case _                              => false

  private def sharing(t: Theory): List[Group] =
    joined(bottom(t).map(id => id -> open(t, id)).filter(_._2.nonEmpty)).map { (ids, opens) =>
      Group.Sharing(ids, opens, ids.flatMap(provided(t, _)).distinct, witnesses(t, ids, opens))
    }

  /** Statements joined while they share an open value, in the model's order. */
  private def joined(xs: List[(NodeId, List[SymbolName])]): List[(List[NodeId], List[SymbolName])] =
    xs.foldLeft(List.empty[(List[NodeId], List[SymbolName])]) { case (groups, (id, opens)) =>
      val (touching, apart) = groups.partition(_._2.exists(opens.contains))
      apart :+ (touching.flatMap(_._1) :+ id, (touching.flatMap(_._2) ++ opens).distinct)
    }

  /** The group solved in substitution order (R14.6): an equation or bound whose other side mentions no value still
    * open witnesses its value, which then stands for itself in the rest; repeated until none is left to solve. What
    * no equation reaches (a cycle, or nothing said) is tested Scala's evidence, or missing. In solving order.
    */
  private def witnesses(t: Theory, ids: List[NodeId], opens: List[SymbolName]): List[Witness] =
    def solve(left: List[SymbolName], solved: List[Witness]): List[Witness] =
      left.iterator.flatMap(s => ids.iterator.flatMap(id => t.node(id).flatMap(_.statement.said)
        .flatMap(f => Equations(left, reach(t, _)).defining(id, f.value, s)))).nextOption() match
        case Some(w) => solve(left.filterNot(_ == w.meaningOf), solved :+ w)
        case None    => solved ++ left.map(s => if tested(t, s) then Witness.Tested(s) else Witness.Missing(s))
    solve(opens, Nil)

  private def tested(t: Theory, s: SymbolName): Boolean =
    t.code.attached.get(s).exists(_.code.scala.nonEmpty)

  /** Each `always` about a store's state (of the state, or of the values it holds), claimed or assumed, with the
    * assumption saying what the state the store starts in meets.
    */
  private def starts(t: Theory): List[Group] = t.nodes.map(_.node).flatMap(n =>
    n.statement.range.filter(_ => n.statement.rule).toList.flatMap(r =>
      Scope.models(t, r).map(m => Group.Start(n.id, Outsides.all(t).collectFirst {
        case (id, OutsideFact.Initially(s, _)) if s == m.name => id
      }))))

  /** `∃ xs, A`: the `i`-th condition of `n`'s claim with the variables above it, written as the claim is. */
  def condition(t: Theory, n: NodeId, i: Int): Option[Written[Expr]] =
    t.node(n).flatMap(_.statement.said).map(f =>
      Written.formula(Conditions.satisfiable(f.term, i), SourceText(s"${f.source.value} (condition ${i + 1})")))

  /** What a condition leaves open, in order: the Definitions and Declarations it mentions, but proven code. */
  def opens(t: Theory, c: Written[Expr]): List[SymbolName] =
    Exprs.mentions(c.value).symbols.filter(s => t.code.attached.get(s).forall(_.code.proven.isEmpty))
