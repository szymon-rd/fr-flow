package keycloak

import frflow.*

// ============================================================================
// The purpose: who a realm's applications accept
// ============================================================================

val Realm = Opaque("Realm", "an organisation using the server, with its own users and applications")
val User  = Opaque("User", "a person with an account in a realm")
val Token = Opaque("Token", "what a user gets when signing in, and hands to a realm's applications")
val Role  = Opaque("Role", "what a realm lets a user do in its applications, such as admin")

val accepted = Param[(Realm.T, Token.T) => Option[(User.T, List[Role.T])]]("whom a realm's application accepts a token as, now: the user, and the roles it is told they have, if it accepts the token at all")
val signedIn = Param[(Realm.T, User.T, Token.T) => Boolean]("whether the user signed in to the realm, with their password while enabled, got the token, and has not signed out with it since")
val enabled = Param[(Realm.T, User.T) => Boolean]("whether the user's account in the realm is enabled now")
val rolesOf = Param[(Realm.T, User.T) => List[Role.T]]("the roles the realm gives the user now")

val realmAccess = Node.claim("A realm's application accepts a token as a user's, with the user's roles, exactly when the user signed in to that realm and got the token, has not signed out with it since, and is still enabled.",
  why = "The idea in one sentence: applications never see passwords, they ask the server whose a token is. Both halves matter: a token must never let anyone else in (no unauthorized access), and a user who signed in must be let in, or a server that accepts nothing would do."
)(forall((r: Term[Realm.T], t: Term[Token.T]) => forall((u: Term[User.T]) =>
  (accepted(r, t) === some((u, rolesOf(r, u)))) === (signedIn(r, u, t) && enabled(r, u)))))

// ============================================================================
// Its two halves: what must never happen, and what users can do
// ============================================================================

val noUnauthorizedAccess = Node.claim("A token is accepted only as a user who signed in to that realm with it, has not signed out since and is still enabled, and only with that user's roles.",
  why = "The safety half of the purpose: whatever an application is told about a token must be true of a sign-in that still stands.",
  idea = "No unauthorized access"
)(forall((r: Term[Realm.T], t: Term[Token.T]) => accepted(r, t).forall(a => signedIn(r, a._1, t) && enabled(r, a._1) && a._2 === rolesOf(r, a._1))))
  .refines(realmAccess)

val signedInAreAccepted = Node.claim("A user who signed in to a realm and got a token, has not signed out with it since and is still enabled, has it accepted there as theirs, with their roles.",
  why = "The capability half of the purpose: a server that turned everyone away would meet the safety half alone.",
  idea = "Signed-in users are let in"
)(forall((r: Term[Realm.T], t: Term[Token.T]) => forall((u: Term[User.T]) =>
  (signedIn(r, u, t) && enabled(r, u)) implies (accepted(r, t) === some((u, rolesOf(r, u)))))))
  .refines(realmAccess)

// ============================================================================
// No unauthorized access, in three independent rules
// ============================================================================

val onlyTheSignedIn = Node.claim("A token is accepted in a realm only as the user who signed in to that realm with it and has not signed out with it since.",
  why = "A token stands for one sign-in: accepting it as anyone else, in another realm, or after its sign-out would let someone in who is not signed in."
)(forall((r: Term[Realm.T], t: Term[Token.T]) => accepted(r, t).forall(a => signedIn(r, a._1, t))))
  .refines(noUnauthorizedAccess)

val disabledHaveNoAccess = Node.claim("A token is never accepted as a user who is disabled now, whenever they signed in.",
  why = "Disabling a user is how an administrator takes access away: it must hold at once, for the sessions the user already has too.",
  idea = "Administering users"
)(forall((r: Term[Realm.T], t: Term[Token.T]) => accepted(r, t).forall(a => enabled(r, a._1))))
  .refines(noUnauthorizedAccess)

val rolesAsGranted = Node.claim("A token is accepted only with the roles the realm gives its user now.",
  why = "Applications decide what a user may do from the roles they are told: a role made up, or kept after the realm took it away, is access the realm did not give."
)(forall((r: Term[Realm.T], t: Term[Token.T]) => accepted(r, t).forall(a => a._2 === rolesOf(r, a._1))))
  .refines(noUnauthorizedAccess)
