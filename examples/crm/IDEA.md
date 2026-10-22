# Shared CRM

Many companies use one CRM, where each company's users keep contacts and deals.
Each user finds by search exactly the stored records of their company and those
currently shared with it, and can add their company's records and share or
unshare them; a share given until a time ends then, and nothing a user does
changes another company's records.

## Finding records

A user may see a record only if it belongs to their company, or if the record's
company has shared it with theirs. Users find records by id, by kind, or list
everything they can see; a search returns every record it asks for that they
may see.

## Sales screen

The sales team has a screen that lists the deals a user can see: every stored
deal that matches their search, and nothing else.

## Writing records

A user can add records for their company, and can share or unshare their
company's records with other companies, for good or until a given time. No
write changes another company's records, or whom they are shared with. A share
names a record by its id, so no two records have one id.

## Expiring shares

A company can share a record until a given time. When that time has passed,
the share ends; nothing else changes.

## Not modelled

- That the account a search or a write runs for is the caller's own
  (authentication).
- That nothing but the CRM's writes and its expiry job changes the database,
  so that the store a search reads is one the CRM reached.

### Writing records

- Editing or removing records.
