# CRM

Many companies use one CRM. Each company's users manage contacts and deals.

## Reading records

A user may see a record only if it belongs to their company, or if the record's
company has shared it with theirs. Users find records by id, by kind, or list
everything they can see.

## Writing records

A user can add records for their company, and can share or unshare their
company's records with other companies. No write changes another company's records, or
adds or removes a share of a record the author's company does not own. Every
share is of a stored record.

## Sales screen

The sales team has a screen that lists the deals a user can see: every stored
deal that matches their search, and nothing else.

## Not modelled

- That the account a search or a write runs for is the caller's own
  (authentication).

### Writing records

- Editing or removing records.
