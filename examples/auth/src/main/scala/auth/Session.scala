package auth

import frflow.*

/** A session: the token issued at login, and the user it was issued to. */
final case class Session(token: String, user: UserId) derives LeanType
