package frflow.eval.term

import frflow.*

/** A record and an enum of the law suite's terms, and two defines over the record, as a model writes them. */
final case class Slot(room: String, start: BigInt, end: BigInt) derives LeanType

enum Kind derives LeanType:
  case Room(name: String, size: BigInt)
  case Desk(n: BigInt)
  case Closed

object Slots:
  val within = define { (s: Term[Slot], t: Term[BigInt]) => s.start <= t && t < s.end }
  val sound = define { (s: Term[Slot]) => s.start < s.end }
