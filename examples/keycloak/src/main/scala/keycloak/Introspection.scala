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

// A token is a reference to a session the server holds, not a statement the application reads.
val referenceTokens = Node.claim("A realm's application accepts a token as the server's introspection of it " +
    "answers.")(
  forall((r: Term[RealmId], t: Term[String]) => accepted(r, t).current === claimsOf(introspect(r, t).result)))
  .refines(onlyTheSignedIn, disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)

// ============================================================================
// What an introspection answers: the claim on `introspect` (owner §40: named apart from the Definition), and its
// five parts, each proven of the introspection's program
// ============================================================================

/** Whether the realm holds the session under the token. */
val heldUnder = define { (st: Term[ServerState], r: Term[RealmId], t: Term[String], x: Term[Session]) =>
  sessions(st, r).contains(x) && x.token === t }

/** Whether `x` is the only session the list holds under its token. */
val onlyOne = define { (ss: Term[List[Session]], x: Term[Session]) =>
  ss.forall(y => (y.token === x.token) implies (y === x)) }

/** Whether `x` is the one session the realm holds under the token. */
val soleUnder = define { (st: Term[ServerState], r: Term[RealmId], t: Term[String], x: Term[Session]) =>
  heldUnder(st, r, t, x) && onlyOne(sessions(st, r), x) }

/** The claims naming a user to a realm's application: the realm, the user, the roles their account there gives. */
val claimsFor = define { (st: Term[ServerState], r: Term[RealmId], u: Term[String]) =>
  make[Claims](r, u, rolesIn(account(st, r, u))) }

/** Whether an answer names only the realm asking. */
val ofRealm = define { (r: Term[RealmId], answer: Term[Option[Claims]]) => answer.forall(c => c.realm === r) }

/** Whether an answer names only a session held under the token, in the realm it names. */
val ofSessionHeld = define { (st: Term[ServerState], t: Term[String], answer: Term[Option[Claims]]) =>
  answer.forall(c => sessions(st, c.realm).contains(make[Session](t, c.realm, c.user))) }

/** Whether an answer names only a user whose account in the realm is enabled. */
val ofEnabledUser = define { (st: Term[ServerState], r: Term[RealmId], answer: Term[Option[Claims]]) =>
  answer.forall(c => isEnabled(account(st, r, c.user))) }

/** Whether an answer gives only the roles the user's account in the realm has. */
val withAccountRoles = define { (st: Term[ServerState], r: Term[RealmId], answer: Term[Option[Claims]]) =>
  answer.forall(c => c.roles === rolesIn(account(st, r, c.user))) }

/** Whether an answer names the user of the one session the realm holds under the token, when they are enabled. */
val forSoleSession = define { (st: Term[ServerState], r: Term[RealmId], t: Term[String],
    answer: Term[Option[Claims]]) =>
  sessions(st, r).forall(x => (soleUnder(st, r, t, x) && isEnabled(account(st, r, x.user))) implies
    (answer === some(claimsFor(st, r, x.user)))) }

// Its formula is the five ideas its parts state, one per line.
val introspectAnswers = Node.claim("An introspection answers as the server's state says of the token's session.")(
  forall((realm: Term[RealmId], token: Term[String]) => let(introspect(realm, token).result)(answer =>
    ofRealm(realm, answer) &&
      ofSessionHeld(state, token, answer) &&
      ofEnabledUser(state, realm, answer) &&
      withAccountRoles(state, realm, answer) &&
      forSoleSession(state, realm, token, answer))))
  .refines(disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)
  .assuming(storeOneAtATime)

val realmIsolation = Node.claim("No application is ever shown claims of a realm other than its own.")(
  forall((asking: Term[RealmId], t: Term[String]) => ofRealm(asking, introspect(asking, t).result)))
  .refines(onlyTheSignedIn, introspectAnswers)
  .assuming(storeOneAtATime)

val answersNameASession = Node.claim("An introspection answers only with the realm and user of a session the " +
    "server holds under the token.")(
  forall((r: Term[RealmId], t: Term[String]) => ofSessionHeld(state, t, introspect(r, t).result)))
  .refines(onlyTheSignedIn, introspectAnswers)
  .assuming(storeOneAtATime)

val answersOnlyEnabled = Node.claim("An introspection names only a user whose account in the realm is enabled.")(
  forall((realm: Term[RealmId], token: Term[String]) => ofEnabledUser(state, realm, introspect(realm, token).result)))
  .refines(introspectAnswers)
  .assuming(storeOneAtATime)

val answersWithRoles = Node.claim("An introspection gives the user's roles as their account in the realm has them.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    withAccountRoles(state, realm, introspect(realm, token).result)))
  .refines(introspectAnswers)
  .assuming(storeOneAtATime)

val answersTheSession = Node.claim("An introspection names the user of the one session the realm holds under the " +
    "token, when they are enabled.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    forSoleSession(state, realm, token, introspect(realm, token).result)))
  .refines(introspectAnswers)
  .assuming(storeOneAtATime)

// ============================================================================
// Looking up a session: the store's index, known only by what is assumed of it
// ============================================================================

/** Whether the realm holds some session under the token. */
val holdsUnder = define { (st: Term[ServerState], r: Term[RealmId], t: Term[String]) =>
  sessions(st, r).exists(x => x.token === t) }

val lookupOnlyHeld = Node.assumption("The store's index returns only a session the realm holds under the token.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    lookup(realm, token).result.forall(x => heldUnder(state, realm, token, x))))

val lookupFindsHeld = Node.assumption("The store's index returns a session whenever the realm holds one under the " +
    "token.")(
  forall((realm: Term[RealmId], token: Term[String]) =>
    holdsUnder(state, realm, token) implies lookup(realm, token).result.isDefined))

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
