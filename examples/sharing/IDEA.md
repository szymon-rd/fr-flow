# Sharing documents

People keep documents in folders and share them with other people, or with
teams. The shares decide who can view a document and who can edit it, and who
may change whom it is shared with.

From: Q1, Q5

## Who can see and change what

A person can view or edit a document; being able to edit it includes being able
to view it. A share gives one person, or everyone in one team, view or edit on
one document, or on a folder and everything inside it, at any depth. Teams
contain people only. Folders form a tree, and a document is in at most one
folder. A person can view a document exactly when some share reaches them and
covers it, and edit it exactly when such a share is an edit share.

Anyone who can edit a document or folder can share it, or unshare it; sharing
it again with the same person or team changes the level. Moving a document into
a folder needs edit on both. Nobody else changes the shares, or where a
document is.

The service answers these questions and makes these changes over HTTP, keeping
the library in memory or in a SQLite file. Versions, deny rules, expiring
shares, audit logs and outside identity providers are not part of it yet.

From: Q1, Q2, Q3, Q4, Q5
