package frflow.protocol
package snapshot

import io.circe.Codec

/** A proof an `always` claim about a store rests on: that a program keeps it (`kept_by_<program>`, `by` the program),
  * or that the store's start meets it (`initially`, `by` the assumption saying what the store starts with).
  */
final case class AlwaysProof(obligation: String, by: String, outcome: Outcome) derives Codec.AsObject
