# Sharing documents

People keep documents in folders and share them with other people, or with
teams. The shares decide who can view a document and who can edit it, and who
may change whom it is shared with. Shares can end, invitations lapse, and
documents in the trash are deleted for good after a while. People can ask for
access; every document has an owner; every change is logged; people are told
of what concerns them; a failure leaves things as they were; and many people
can use it at once.

From: Q1, Q5, Q17

## Who can see and change what

A person can view or edit a document; being able to edit it includes being able
to view it. A share gives one person, or everyone in one team, view or edit on
one document, or on a folder and everything inside it, at any depth. Teams
contain people only. Folders form a tree, and a document is in at most one
folder. A person can view a document exactly when some share in force reaches
them and covers it and the document is not in the trash, and edit it exactly
when such a share is an edit share.

Anyone who can edit a document or folder can share it, or unshare it; sharing
it again with the same person or team changes the level. Moving a document into
a folder needs edit on both. Nobody else changes the shares, or where a
document is. Moving a document out of a folder may take away the mover's own
access, and the last edit share of a document may be unshared.

From: Q1, Q2, Q3, Q4, Q10, Q11

## Expiring shares

A share may be given until a time. From that time on it gives no access,
whether or not housekeeping has removed it yet: access is worked out from the
clock when it is asked. Sharing again replaces the end time.

From: Q6

## Invitations

Anyone who can edit a document or folder can invite a person to it, at a level,
and withdraw the invitation. An invitation gives no access until the person
accepts it; accepting it makes the share. An invitation can be accepted for 7
days after it is sent; then it lapses, and housekeeping removes it.

From: Q7

## Trash

Deleting a document puts it in the trash, where it gives nobody access, whatever
its shares. Anyone who can edit it can restore it for 30 days, and its shares
hold again. After 30 days it is gone: it can no longer be restored, and
housekeeping deletes it and its shares for good, never before.

From: Q8

## Time and housekeeping

Time is the server's clock, in seconds, read once for each request: a request
is answered at one moment. Housekeeping runs every minute, as one transaction
beside the requests; it removes shares that have ended, invitations that have
lapsed, and documents gone from the trash. Nothing waits for it: it only tidies.

From: Q9

## Serving

The service answers these questions and makes these changes over HTTP, keeping
the library in memory or in a SQLite file. Versions, deny rules and outside
identity providers are not part of it yet.

From: Q5

## Access requests

Anyone named in the library can ask for view or edit on a document or a
folder. Asking gives no access. Anyone who can edit it approves the request,
which makes the share asked for, or declines it. A request nobody answers is
reminded of to the owner of each document it is for after 48 hours, once, and
declined automatically after 7 days; housekeeping does both.

From: Q12

## Ownership

Every document has exactly one owner. Only the owner, while they can edit it,
hands it on, and only to someone who can edit it; the new owner then has an
edit share of it for good. Nobody can unshare or replace an owner's own share
of their document, not by sharing, accepting an invitation or approving a
request, so the owner always can edit it, and leaving a team never takes their
documents from them.

From: Q14

## Audit

Every change is logged with who asked, what and when, in the same save as the
change, so no change is seen before its entry. Every yes of "can view" can be
traced to the log entries of the shares that gave it. Entries are never taken
away; after a year, housekeeping forgets what an entry tells, unless it is the
making of a share still held or of a change a waiting notice tells of.

From: Q15

## Notifications

Invitations, accepted invitations, access requests and their answers,
reminders, documents handed on, and shares ending within a day are notified to
the person they concern.
Each notice goes to an outbox in the same save as its change, and is sent from
there, retried until the mail server has it: a person is told of each event at
least once and never twice, because the mail server keeps each event once.
Four notices are sent at once, each person's in order: a run sends the oldest
notice of each person, and the next run the next.

From: Q13

## Failures

When the store fails in the middle of a request, the request is answered 503
and changes nothing: each request is one save. A run of housekeeping that fails
changes nothing and is tried again at the next minute; a run of delivery that
fails leaves its notice in the outbox, to be sent again.

From: Q16

## Concurrency

Many people use the service at once. Each request, and each run of
housekeeping, is one transaction on the store: two requests on one document at
once leave it as one after the other does, in the order they were made to the
store, and housekeeping comes before or after a request, never in the middle.
Delivery runs beside the requests: it only takes notices out of the outbox,
each in a transaction of its own, while requests only add to it. The service is
one process with one store.

From: Q17, Q18, Q19, Q20, Q21, Q22
