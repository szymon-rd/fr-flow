package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Reliance, Statement}
import frflow.proof.terms.{OpenTerms, TermTable}

/** The root's `idle` try: the root with every operation its statement names doing nothing, but the words left open
  * above (`.leftOpenAbove`), which it must hold for whatever they mean. Within Lean's default budget.
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
    r.theory.refinement.nodes.map(_.statement).filter(_.operation.contains(s))

  private def leftOpen(s: Statement): Boolean = s match
    case Statement.Contract(_, _, Reliance.LeftOpen)        => true
    case Statement.FlowContract(_, _, _, Reliance.LeftOpen) => true
    case _                                                  => false
