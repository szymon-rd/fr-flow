package auth

import frflow.*

/** Who a user is: their id. */
final case class UserId(name: String) derives LeanType
