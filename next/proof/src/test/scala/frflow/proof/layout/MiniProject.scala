package frflow.proof.layout

import frflow.core.Booking
import frflow.core.consistency.Vacuity
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{Constant, NodeObligations, Obligation, Obligations}
import frflow.proof.terms.TermTable
import frflow.proof.whole.{ExampleGoals, Joint, Possible}

/** Mini's Lean: its obligations, those of the theory as a whole (the witness search's value for `endsAfterStart`
  * given), and every module `LeanProject` lays out.
  */
object MiniProject:
  lazy val table: TermTable = TermTable.of(Mini.resolved)
  lazy val nodes: List[NodeObligations] = Obligations.of(Mini.resolved, table, Set.empty)
  lazy val whole: List[Obligation] = Joint.of(Mini.resolved) ++
    Possible.of(Mini.resolved, Map(Vacuity.Inhabited(Mini.endsAfterStartId, Booking.ty) ->
      List(Constant(Mini.booking, Booking.ty)))) ++ ExampleGoals.of(Mini.resolved, Mini.examples)
  lazy val modules: List[LeanModule] = LeanProject.of(Mini.resolved, table, nodes, whole)
