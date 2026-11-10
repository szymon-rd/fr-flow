package payments

import frflow.*

/** An account: its id, the user who owns it, and its balance in whole cents. */
final case class Account(id: String, owner: String, balance: BigInt) derives LeanType
