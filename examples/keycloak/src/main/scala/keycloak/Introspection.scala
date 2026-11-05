package keycloak

import frflow.*

// ============================================================================
// Checking tokens: applications ask the server whose a token is
// ============================================================================

/** What the server tells a realm's application about a token: the realm, the user, their realm roles. */
final case class Claims(realm: RealmId, user: String, roles: List[String]) derives LeanType

val introspect = Definition[(RealmId, String) => Flow[Option[Claims]]]("the server's answer to a realm's " +
  "application asking about a token: the claims it is active with, or none (not active)")

/** The user and roles an answer names, if any. */
val claimsOf = define { (c: Term[Option[Claims]]) =>
  c.fold(none[Acceptance])(x => some(make[Acceptance](x.user, x.roles))) }

val referenceTokens = Node.claim("A realm's application accepts a token as the server's introspection of it " +
    "answers: a token is a reference to a session the server holds, not a statement the application reads.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).current === claimsOf(introspect(r, t).result)))
  .refines(onlyTheSignedIn, disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)

val realmIsolation = Node.claim("No application is ever shown claims of a realm other than its own.")(
  forall((asking: Term[RealmId], t: Term[String]) => introspect(asking, t).result.forall(c => c.realm === asking)))
  .refines(onlyTheSignedIn)
  .assuming(storeOneAtATime)

val answersNameASession = Node.claim("An introspection answers only with the realm and user of a session the " +
    "server holds under the token.")(
  forall((r: Term[RealmId], t: Term[String]) => introspect(r, t).result.forall(c =>
    sessions(state, c.realm).contains(make[Session](t, c.realm, c.user)))))
  .refines(onlyTheSignedIn)
  .assuming(storeOneAtATime)

/** Whether `x` is the only session the list holds under its token. */
val onlyOne = define { (ss: Term[List[Session]], x: Term[Session]) =>
  ss.forall(y => (y.token === x.token) implies (y === x)) }

/** The claim on `introspect` (owner §40: named apart from the Definition). */
val introspectAnswers = Node.claim("An introspection names the realm asking, and a user enabled there with their " +
    "roles, only for a session that realm holds under the token; and it names that session's user whenever the " +
    "user is enabled and the token names no other session there.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    introspect(realm, token).result.forall(c => c.realm === realm &&
      sessions(state, c.realm).contains(make[Session](token, c.realm, c.user)) &&
      isEnabled(account(state, realm, c.user)) && c.roles === rolesIn(account(state, realm, c.user))) &&
    sessions(state, realm).forall(x =>
      (x.token === token && isEnabled(account(state, realm, x.user)) && onlyOne(sessions(state, realm), x)) implies
        (introspect(realm, token).result === some(make[Claims](realm, x.user,
          rolesIn(account(state, realm, x.user))))))))
  .refines(answersNameASession, disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted, realmIsolation)
  .assuming(storeOneAtATime)

// ============================================================================
// Looking up a session: the store's index, known only by what is assumed of it
// ============================================================================

val sessionLookup = Node.assumption("The store's index returns a session it holds under the token in the realm " +
    "asked, if it holds one, and never one of another realm or token.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    lookup(realm, token).result.forall(x =>
      sessions(state, realm).contains(x) && x.token === token && x.realm === realm) &&
      (sessions(state, realm).exists(x => x.token === token) implies lookup(realm, token).result.isDefined)))

val lookupKeeps = Node.assumption("Looking a token up changes nothing the store holds.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    serverStore.in(lookup(realm, token).after) === serverStore.current))

/** An introspection: the realm's session the token names, if its user is enabled there, with their roles. */
val introspecting = program { (realm: Term[RealmId], token: Term[String]) =>
  for
    found <- lookup(realm, token)
    s     <- load
  yield found.fold(none[Claims])(x => accountOf(s.accounts, realm, x.user).fold(none[Claims])(a =>
    when(a.enabled)(some(make[Claims](realm, x.user, a.roles))).otherwise(none[Claims]))) }
