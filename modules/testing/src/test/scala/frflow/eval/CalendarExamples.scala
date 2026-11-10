package frflow.eval

import frflow.*
import frflow.eval.Calendar.{Booking, RoomBookings, granted, grantedCode, noOverlap}

/** The calendar's examples: a fact about lifted code is plain Scala too (`lifted { … }` of a closed expression),
  * and one about the Definition it is given to is written as any example is.
  */
class CalendarExamples extends FrFlowExamples(Calendar.model):
  example("back to back: no overlap"):
    lifted { noOverlap(Booking("Oak", BigInt(9), BigInt(10)), Booking("Oak", BigInt(10), BigInt(11))) }

  example("the code grants a request beside a booking, and refuses one inside it"):
    lifted {
      grantedCode(RoomBookings("Oak", List(Booking("Oak", BigInt(9), BigInt(11)))),
        Booking("Oak", BigInt(11), BigInt(12))) &&
      !grantedCode(RoomBookings("Oak", List(Booking("Oak", BigInt(9), BigInt(11)))),
        Booking("Oak", BigInt(10), BigInt(12)))
    }

  example("overlapping: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
