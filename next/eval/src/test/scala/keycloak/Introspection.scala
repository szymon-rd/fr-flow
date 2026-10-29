package keycloak

import frflow.*

// ============================================================================
// Checking tokens: applications ask the server whose a token is
// ============================================================================

/** What the server tells a realm's application about a token: the realm, the user, their realm roles. */
final case class Claims(realm: RealmId, user: String, roles: List[String]) derives LeanType

val introspect = Definition[(RealmId, String) => Option[Claims]]("the server's answer to a realm's application " +
  "asking about a token: the claims it is active with, or none (not active)")

/** The user and roles an answer names, if any. */
val claimsOf = define { (c: Term[Option[Claims]]) =>
  c.fold(none[Acceptance])(x => some(make[Acceptance](x.user, x.roles))) }

val referenceTokens = Node.claim("A realm's application accepts a token as the server's introspection of it " +
    "answers: a token is a reference to a session the server holds, not a statement the application reads.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t) === claimsOf(introspect(r, t))))
  .refines(realmAccess)

val realmIsolation = Node.claim("No application is ever shown claims of a realm other than its own.")(
  forall((asking: Term[RealmId], t: Term[String]) => introspect(asking, t).forall(c => c.realm === asking)))
  .refines(onlyTheSignedIn)

val answersNameASession = Node.claim("An introspection answers only with the realm and user of a session the " +
    "server holds under the token.")(
  forall((r: Term[RealmId], t: Term[String]) =>
    introspect(r, t).forall(c => sessions(c.realm).contains(make[Session](t, c.realm, c.user)))))
  .refines(onlyTheSignedIn)

/** Whether `x` is the only session the list holds under its token. */
val onlyOne = define { (ss: Term[List[Session]], x: Term[Session]) =>
  ss.forall(y => (y.token === x.token) implies (y === x)) }

/** The claim on `introspect` (owner §40: named apart from the Definition). */
val introspectAnswers = Node.claim("An introspection names the realm asking, and a user enabled there with their " +
    "roles, only for a session that realm holds under the token; and it names that session's user whenever the " +
    "user is enabled and the token names no other session there.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    introspect(realm, token).forall(c => c.realm === realm &&
      sessions(c.realm).contains(make[Session](token, c.realm, c.user)) &&
      isEnabled(account(realm, c.user)) && c.roles === rolesIn(account(realm, c.user))) &&
    sessions(realm).forall(x =>
      (x.token === token && isEnabled(account(realm, x.user)) && onlyOne(sessions(realm), x)) implies
        (introspect(realm, token) === some(make[Claims](realm, x.user, rolesIn(account(realm, x.user))))))))
  .refines(answersNameASession, disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted, realmIsolation)

// ============================================================================
// Looking up a session: the store, outside the proven core
// ============================================================================

val lookup = Definition[(RealmId, String) => Option[Session]]("the store's answer to looking up a token's session " +
  "in a realm, from its index by realm and token")

val sessionLookup = Node.assumption("The store's index returns a session it holds under the token in the realm " +
    "asked, if it holds one, and never one of another realm or token.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    lookup(realm, token).forall(x => sessions(realm).contains(x) && x.token === token && x.realm === realm) &&
      (sessions(realm).exists(x => x.token === token) implies lookup(realm, token).isDefined)))

/** An introspection: the realm's session the token names, if its user is enabled there, with their roles. */
def introspection(lookUp: (RealmId, String) => Option[Session], accountOf: (RealmId, String) => Option[UserAccount])(
    realm: RealmId, token: String): Option[Claims] =
  for
    x <- lookUp(realm, token)
    a <- accountOf(realm, x.user) if a.enabled
  yield Claims(realm, x.user, a.roles)
