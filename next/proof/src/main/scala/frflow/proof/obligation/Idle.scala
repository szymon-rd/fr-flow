package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Reliance, Statement}
import frflow.proof.terms.{OpenTerms, TermTable}

/** A root's `idle` try: the root statement with every Definition it names doing nothing, but the words left open
  * above (`.leftOpenAbove`), which it must hold for whatever they mean. Within Lean's default budget. A root about a
  * program (rooms' `BookWhenFree`) has none: a run has no "nothing" to give (`Substitute.canDoNothing`).
  */
object Idle:
  val DefaultHeartbeats: Int = 200000

  def of(r: Resolved, table: TermTable, n: NodeId): Option[Obligation] =
    if !r.theory.refinement.roots.exists(_.id == n) then None
    else
      val ops = table.claims.getOrElse(n, OpenTerms.empty).symbols
        .filter(s => onOperation(r, s).exists(!leftOpen(_)) && Substitute.canDoNothing(table.typeOf(s)))
      Option.when(ops.nonEmpty)(Obligation(ObligationName.Tried(TryKind.Idle),
        Prop.over(Nil, Prop.ClaimOf(n, ops.map(_ -> Substitute.Nothing).toMap)), Discharge.Attempt(DefaultHeartbeats),
        s"${n.value} is met by doing nothing (${ops.map(_.value).sorted.mkString(", ")}: returning nothing)."))

  private def onOperation(r: Resolved, s: SymbolName): List[Statement] =
    r.theory.refinement.nodes.map(_.statement).filter(_.definition.contains(s))

  private def leftOpen(s: Statement): Boolean = s.relied == Reliance.LeftOpen
