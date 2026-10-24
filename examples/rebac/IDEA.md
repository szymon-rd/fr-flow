# Relationship-based access

A service that answers whether a person may do something to an object, from
relationship tuples and a schema, in the style of Google Zanzibar and OpenFGA.
A check of whether a person has a relation to an object, at a version, answers
yes exactly when the tuples stored at that version give it under the schema,
within the resolution depth.

## Checks

From: Q1, Q3

A check names an object, a relation and a person, and the version it reads.
Tuples say who has which relation on which object: `doc:readme#viewer@user:ann`.
Groups and folders nest, so a check may follow several steps; it follows at most
the configured resolution depth (25 steps by default, as OpenFGA), and what is
given only in more steps is answered no. The service also writes and deletes
tuples.

## The schema

From: Q2

For each kind of object, the schema names its relations and the rules that give
each: the relation's own tuples; a userset as the subject of a tuple
(`group:eng#member`: everyone who is a member of the group); a relation implied
by another on the same object (an editor is a viewer); and a relation inherited
through a link (a document's viewers include the viewers of its parent folder).

## Versions and the cache

From: Q4

Each write and delete gets the next version. A check answers from the tuples
the writes up to its version leave, never from another version's. A cache may
answer checks it has answered before, but never with an answer of another
version.

## Not modelled

From: Q5

Schema changes over time (the schema is fixed); exclusion, intersection and
conditions; who may write tuples; listing the users of an object; a watch API;
replication across regions.
