package frflow.proof.obligation.tried

import cats.data.NonEmptyList
import frflow.core.analysis.{Constrained, Resolved}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Range, Reliance, Statement}
import frflow.proof.obligation.{Discharge, Obligation, ObligationName, Prop, Substitute, TryKind}
import frflow.proof.terms.{OpenTerms, TermTable}

/** A root's `idle` try: the root statement with every Definition it names doing nothing, but the words left open
  * above (`.leftOpenAbove`), which it must hold for whatever they mean; a Declaration is no code, so doing nothing is
  * no meaning of it. Asked of the roots naming those Definitions together: the purpose is met by doing nothing only
  * when each of them is, and a safety root alone met by doing nothing is no defect (step 12 ruling); the others are
  * stated by their formulas, so no root's module imports another's. Within Lean's
  * default budget. A root about a
  * program (rooms' `BookWhenFree`) has none: a run has no "nothing" to give (`Substitute.canDoNothing`).
  */
object Idle:
  val DefaultHeartbeats: Int = 200000

  def of(r: Resolved, table: TermTable, n: NodeId): Option[Obligation] =
    if !r.theory.refinement.roots.exists(_.id == n) then None
    else
      val ops = table.claims.getOrElse(n, OpenTerms.empty).symbols
        .filter(s => !Constrained.isDeclaration(r.theory, s) && onOperation(r, s).exists(!leftOpen(_)) &&
          Substitute.canDoNothing(table.typeOf(s)))
      val together = n :: roots(r).filter(x => x != n &&
        table.claims.getOrElse(x, OpenTerms.empty).symbols.exists(ops.contains))
      val nothing = ops.map(_ -> Substitute.Nothing).toMap
      Option.when(ops.nonEmpty)(Obligation(ObligationName.Tried(TryKind.Idle),
        Prop.over(Nil, Prop.Both(NonEmptyList(Prop.ClaimOf(n, nothing), together.tail.flatMap(x =>
          r.theory.node(x).flatMap(_.statement.said).map(Prop.Formula(_, nothing)).toList)))),
        Discharge.Attempt(DefaultHeartbeats), s"${together.map(_.value).mkString(", ")} ${
          if together.size == 1 then "is" else "are together"} met by doing nothing (${
          ops.map(_.value).sorted.mkString(", ")}: returning nothing)."))

  /** The roots stated over every possible value: the purpose's statements. */
  private def roots(r: Resolved): List[NodeId] = r.theory.refinement.roots
    .filter(x => x.statement.stated && x.statement.range.contains(Range.Possible) && !x.statement.rule).map(_.id)

  private def onOperation(r: Resolved, s: SymbolName): List[Statement] =
    r.theory.refinement.nodes.map(_.statement).filter(_.definition.contains(s))

  private def leftOpen(s: Statement): Boolean = s.relied == Reliance.LeftOpen
