package rooms

import frflow.*
import frflow.dsl.term.Lift

// The constructs a typed final encoding has to design (R8.2), written as a model writes them: a match over an enum
// (each arm over the case's fields), a record made and updated, a fold, an option's fold, an either's, a `let`.

enum Change derives LeanType:
  case Book(b: Booking)
  case Cancel(room: String, start: BigInt)
  case Clear

val afterChange = define { (held: Term[List[Booking]], c: Term[Change]) =>
  c.on[Change.Book](b => b :: held)
    .on[Change.Cancel]((room, start) => held.filter(b => !(b.room === room && b.start === start)))
    .on(Change.Clear)(Lift.constant(List.empty[Booking])) }

val moved = define { (b: Term[Booking], t: Term[BigInt]) =>
  b.updated(_.start, t).updated(_.end, t + (b.end - b.start)) }

val booked = define { (held: Term[List[Booking]]) => held.foldLeft(0: Term[BigInt])((n, b) => n + (b.end - b.start)) }

val hourLong = define { (room: Term[String], t: Term[BigInt]) =>
  let(make[Booking](room, t, t + 1))(b => b.end - b.start) }

val startOr = define { (o: Term[Option[Booking]], t: Term[BigInt]) => o.fold(t)(b => b.start) }

val outcome = define { (e: Term[Either[String, Booking]], t: Term[BigInt]) => e.fold(_ => t, b => b.end) }
