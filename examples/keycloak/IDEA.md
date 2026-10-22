# Realms: a small authentication server

A realm's application accepts a token as a user's, with the user's roles,
exactly when the user signed in to that realm with their password and got the
token, has not signed out with it since, and is still enabled.

Several organisations share one authentication server, like Keycloak. Each
organisation is a realm with its own users and applications. Applications
never see passwords: they send users to the server to sign in, and ask the
server whose a token is.

## No unauthorized access

A token never lets anyone in who is not signed in with it: not another user,
not in another realm, not after its sign-out, not once the user is disabled,
and never with roles the realm did not give.

## Signed-in users are let in

A user who signed in and has neither signed out nor been disabled has their
token accepted, with their roles. A server that turns everyone away is no
authentication server.

## Signing in and out

A user of a realm can sign in with their username and password. If the user
is enabled and the password is theirs, the server opens a session and gives
back its token, a value no other session has. Anyone else gets no session.

A user can sign out with their token: its session ends at once.

## Checking tokens

An application of a realm can ask the server whose a token is. The server
answers with the user and their roles in that realm when the token's session
is open in that realm and the user is enabled; otherwise the token is not
active.

## Realms

A token is only ever good in the realm that issued it, and no application is
ever shown anything of another realm.

## Administering users

Realms and their users are loaded at start. An administrator can enable or
disable a user; the next request sees it, and a disabled user's tokens stop
being accepted at once.

## Not modelled

- How passwords are hashed: the server compares stored hashes, computed with
  each user's salt before a request reaches the core.
- How tokens are drawn: 256 random bits each, trusted to be new.
- Token expiry and refresh tokens.
- Which applications may ask (client authentication), consent, and the
  OpenID Connect discovery documents.
- Creating realms and users, and changing passwords or roles.
