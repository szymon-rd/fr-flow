# Sharing documents

People keep documents in folders and share them with other people, or with
teams. The shares decide who can view a document and who can edit it, and who
may change whom it is shared with. Shares can end, invitations lapse, and
documents in the trash are deleted for good after a while.

From: Q1, Q5

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
is answered at one moment. Housekeeping runs every minute, one at a time with
the requests; it removes shares that have ended, invitations that have lapsed,
and documents gone from the trash. Nothing waits for it: it only tidies.

From: Q9

## Serving

The service answers these questions and makes these changes over HTTP, keeping
the library in memory or in a SQLite file. Versions, deny rules, audit logs and
outside identity providers are not part of it yet.

From: Q5
