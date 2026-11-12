package frflow.proof.lean.laws

import frflow.core.Booking
import frflow.core.name.KbName
import frflow.proof.lean.lower.LowerEnv

/** The lowering environment of the laws' terms: a FrModel `Laws` over bookings and events. */
object LawsEnv:
  val env: LowerEnv = LowerEnv(KbName("Laws"), _ => Nil,
    n => List(Booking.data, MoreTerms.event).find(_.typeName == n))
