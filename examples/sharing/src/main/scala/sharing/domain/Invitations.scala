package sharing.domain

import frflow.*

/** An invitation to a document or folder: sent to a person by someone, at a level, at a time (in seconds). It gives no
  * access: accepting it, while it is open, makes the share. It is pending until accepted, withdrawn or lapsed.
  */
final case class Invitation(to: PersonId, what: Target, level: Level, by: PersonId, sent: BigInt)
object Invitation extends Data[Invitation]:
  given LeanType[Invitation] = LeanType.product[Invitation]
