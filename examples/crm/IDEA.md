# Shared CRM

Many companies use one CRM, where each company's users keep contacts and deals.
A user's search finds a record exactly when it asks for that record, a user of
the record's company added it, and it is of the user's company or currently
shared with it by its own. Users add their company's records, and share them
with other companies, for good or until a time, or unshare them. Nothing a user
does changes what anyone finds of another company's records.

## Finding records

A user may see a record only if it belongs to their company, or if the record's
company has shared it with theirs and the share's time, if it has one, has not
come. Users find records by id, by kind, or list everything they can see; a
search returns every record it asks for that they may see, of what the CRM holds
when it runs: what its writes and its expiry job have done so far.

## Sales screen

The sales team has a screen that lists the deals a user can see: every stored
deal that matches their search, and nothing else.

## Writing records

A user can add records for their company, and can share or unshare their
company's records with other companies, for good or until a given time; sharing
again replaces the time. The CRM holds exactly the records its users added, and
holds a share exactly as long as the last share or unshare of it says and its
time has not come: a write does what its author asked, and nothing else, and
removes no record. A record a user adds is found by their searches from then on.
No write changes another company's records, or whom they are shared with. A
share names a record by its id, so no two records have one id: a record is not
added under an id another record has.

## Expiring shares

A company can share a record until a given time. When that time has passed,
the share ends: searches no longer find the record through it, whether or not
the expiry job has run. The job clears ended shares every minute, and changes
nothing else.

## Not modelled

- That the account a search or a write runs for is the caller's own
  (authentication).
- That the database's tables, which the running read side reads, are what its
  event log led to: that nothing but the write side and the expiry job changes
  them (a test replays the log).
- Editing or removing records: a write only adds one.
