# Realms: a small authentication server

Several organisations share one authentication server, like Keycloak. Each
organisation is a realm with its own users. Applications never see passwords:
they send users to the server to sign in, and ask the server whose a token is.

## Signing in and out

A user of a realm can sign in with their username and password. If the user
is enabled and the password is theirs, the server opens a session and gives
back its token, a value no other session has. Anyone else gets no session.

A user can sign out with their token: its session ends at once.

## Checking tokens

An application of a realm can ask the server whose a token is. The server
answers with the user and their roles in that realm exactly when the token's
session is open in that realm and the user is still enabled; otherwise the
token is not active.

A token is only ever good in the realm that issued it.

## Not modelled

- How passwords are hashed: the server compares stored hashes, computed with
  each user's salt before a request reaches the core.
- Token expiry and refresh tokens.
- Which applications may ask (client authentication), consent, and the
  OpenID Connect discovery documents.
- Managing realms and users: they are loaded at start, and an administrator
  can enable or disable a user.
