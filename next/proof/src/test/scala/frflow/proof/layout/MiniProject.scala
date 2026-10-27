package frflow.proof.layout

import frflow.core.Booking
import frflow.core.consistency.Vacuity
import frflow.proof.obligation.Constant

/** Mini's Lean, the witness search's value for `endsAfterStart` given. */
val MiniProject: Laid = Laid(Mini.resolved, Map(Vacuity.Inhabited(Mini.endsAfterStartId, Booking.ty) ->
  List(Constant(Mini.booking, Booking.ty))), Mini.examples)

val ProgramsProject: Laid = Laid(Programs.resolved, Map.empty, Nil)
