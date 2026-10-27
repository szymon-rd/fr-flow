package frflow.proof.lean.laws

import frflow.core.{Booking, Lang}
import frflow.core.name.KbName
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.LowerEnv

/** The lowering environment of the laws' terms: a knowledge base `Laws` over bookings and events. */
object LawsEnv:
  val env: LowerEnv = LowerEnv(KbName("Laws"), _ => Nil, _ => Names.builtin("stored"),
    _ => Names.builtin("Bookings"), n => List(Booking.data, MoreTerms.event).find(_.typeName == n),
    _ => Some(Lang.big))
