package keycloak

import frflow.*

// Keycloak's nodes in the three kinds (owner §15), each named as today's. The purpose's words (`accepted`,
// `signedIn`, `enabled`, `rolesOf`) are Declarations; today's definition nodes are claims, each an equation tying
// one of them to the domain; realms are `RealmId`s, users their usernames, tokens and roles strings (today's
// `identities` fixed four open types to these, which the types now say directly).

// ============================================================================
// The purpose: who a realm's applications accept
// ============================================================================

final case class RealmId(name: String) derives LeanType

/** Whom an application accepts a token as: the user, and the roles it is told they have. */
final case class Acceptance(user: String, roles: List[String]) derives LeanType

val accepted = Declaration[(RealmId, String) => Option[Acceptance]]("whom a realm's application accepts a token " +
  "as, now: the user, and the roles it is told they have, if it accepts the token at all")
val signedIn = Declaration[(RealmId, String, String) => Boolean]("whether the user signed in to the realm, with " +
  "their password while enabled, got the token, and has not signed out with it since")
val enabled = Declaration[(RealmId, String) => Boolean]("whether the user's account in the realm is enabled now")
val rolesOf = Declaration[(RealmId, String) => List[String]]("the roles the realm gives the user now")

val realmAccess = Node.claim("A realm's application accepts a token as a user's, with their roles, exactly when " +
    "the user is signed in there with it and enabled.")(
  forall((r: Term[RealmId], t: Term[String], u: Term[String]) =>
    (accepted(r, t) === some(make[Acceptance](u, rolesOf(r, u)))) === (signedIn(r, u, t) && enabled(r, u))))

// ============================================================================
// Its two halves: what must never happen, and what users can do
// ============================================================================

// Its formula is its three parts' formulas, one per line: a define cannot read a Declaration, so they are not named.
val noUnauthorizedAccess = Node.claim("A token is accepted only as its user is authorized now.")(
  forall((r: Term[RealmId], t: Term[String]) =>
    accepted(r, t).forall(a => signedIn(r, a.user, t)) &&
      accepted(r, t).forall(a => enabled(r, a.user)) &&
      accepted(r, t).forall(a => a.roles === rolesOf(r, a.user))))
  .refines(realmAccess)

val signedInAreAccepted = Node.claim("A user signed in to a realm with a token, and enabled, has it accepted there " +
    "as theirs, with their roles.")(
  forall((r: Term[RealmId], t: Term[String], u: Term[String]) =>
    (signedIn(r, u, t) && enabled(r, u)) implies (accepted(r, t) === some(make[Acceptance](u, rolesOf(r, u))))))
  .refines(realmAccess)

// ============================================================================
// No unauthorized access, in three independent rules
// ============================================================================

val onlyTheSignedIn = Node.claim("A token is accepted in a realm only as the user signed in there with it.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).forall(a => signedIn(r, a.user, t))))
  .refines(noUnauthorizedAccess)

val disabledHaveNoAccess = Node.claim("A token is never accepted as a user who is disabled now.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).forall(a => enabled(r, a.user))))
  .refines(noUnauthorizedAccess)

val rolesAsGranted = Node.claim("A token is accepted only with the roles the realm gives its user now.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).forall(a => a.roles === rolesOf(r, a.user))))
  .refines(noUnauthorizedAccess)
