# Auth

A system decides which users may access which resources. No user may ever
access a resource they are not authorized to access.

Users identify themselves with tokens they receive at login. Authorization is
given by a table of grants: a user may access a path when a grant names that
user and that path.

## Not modelled

- How tokens are issued at login, and when they expire.
- Who may change the table of grants.
