package keycloak

import examples.Folds.*
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

val realmAccess = Node.claim("A realm's application accepts a token as a user's, with the user's roles, exactly " +
    "when the user signed in to that realm and got the token, has not signed out with it since, and is still " +
    "enabled.")(
  forall((r: Term[RealmId], t: Term[String], u: Term[String]) =>
    (accepted(r, t) === some(make[Acceptance](u, rolesOf(r, u)))) === (signedIn(r, u, t) && enabled(r, u))))

// ============================================================================
// Its two halves: what must never happen, and what users can do
// ============================================================================

val noUnauthorizedAccess = Node.claim("A token is accepted only as a user who signed in to that realm with it, has " +
    "not signed out since and is still enabled, and only with that user's roles.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).noneOr(a =>
    signedIn(r, a.user, t) && enabled(r, a.user) && a.roles === rolesOf(r, a.user))))
  .refines(realmAccess)

val signedInAreAccepted = Node.claim("A user who signed in to a realm and got a token, has not signed out with it " +
    "since and is still enabled, has it accepted there as theirs, with their roles.")(
  forall((r: Term[RealmId], t: Term[String], u: Term[String]) =>
    (signedIn(r, u, t) && enabled(r, u)) implies (accepted(r, t) === some(make[Acceptance](u, rolesOf(r, u))))))
  .refines(realmAccess)

// ============================================================================
// No unauthorized access, in three independent rules
// ============================================================================

val onlyTheSignedIn = Node.claim("A token is accepted in a realm only as the user who signed in to that realm with " +
    "it and has not signed out with it since.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).noneOr(a => signedIn(r, a.user, t))))
  .refines(noUnauthorizedAccess)

val disabledHaveNoAccess = Node.claim("A token is never accepted as a user who is disabled now, whenever they " +
    "signed in.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).noneOr(a => enabled(r, a.user))))
  .refines(noUnauthorizedAccess)

val rolesAsGranted = Node.claim("A token is accepted only with the roles the realm gives its user now.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).noneOr(a => a.roles === rolesOf(r, a.user))))
  .refines(noUnauthorizedAccess)
