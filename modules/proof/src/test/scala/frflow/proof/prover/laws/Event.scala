package frflow.proof.prover.laws

/** The laws' sum type: a room booked at a moment, or cleared. */
enum Event:
  case Booked(at: BigInt)
  case Cleared
