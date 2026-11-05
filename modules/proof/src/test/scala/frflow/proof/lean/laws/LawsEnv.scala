package frflow.proof.lean.laws

import frflow.core.{Booking, Lang}
import frflow.core.name.KbName
import frflow.proof.lean.ast.{LExpr, Names}
import frflow.proof.lean.lower.LowerEnv

/** The lowering environment of the laws' terms: a FrModel `Laws` over bookings and events. */
object LawsEnv:
  val env: LowerEnv = LowerEnv(KbName("Laws"), _ => Nil, _ => Names.builtin("stored"),
    op => LExpr.Const(List(Names.builtin("Bookings"), Names.ident(op.value))),
    n => List(Booking.data, MoreTerms.event).find(_.typeName == n),
    _ => Some(Lang.big))
