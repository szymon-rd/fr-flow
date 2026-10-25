# Sharing

People keep documents in folders and share them with people or teams, to view or to edit. The idea is in
[IDEA.md](IDEA.md); the root, `AccessFollowsShares` (`Purpose.scala`), says the shares in force decide access
exactly, and that only an editor, an open invitation taken up, or housekeeping clearing what has ended changes them.
Branches say how: `InvitationsAreOffers` (`invitations/`), `TrashUntilGone` (`trash/`),
`HousekeepingClearsOnlyTheEnded` (`housekeeping/`), `AccessRequestsAreAsks` (`requests/`), `OwnersKeepTheirDocuments`
(`ownership/`), `AuditTrail` (`audit/`) and `NoticesFollowChanges` (`notifications/`). The root is timeless, and the branches name no lifetime: "in force", "open" and
"gone" are left open there and fixed with the clock in `time/Lifetimes.scala`; the deadlines (`time/Deadlines.scala`)
sit below the branches whose proofs use them.

## Where things are

| Package | What is in it |
|---|---|
| `sharing.domain` | the data: people, teams, documents, folders, shares, the library |
| `sharing` (`Purpose.scala`) | the meaning (Reach, Cover, Permission) and the root |
| `sharing.service` | `trait Sharing`, the service; `object Sharing`, one contract per method, each with its proven code; `SharingService` runs it |
| `sharing.invitations` | `trait Invitations` (invite, accept, withdraw); `object Invitations`, the branch `InvitationsAreOffers` and the contracts; `InvitationsService` |
| `sharing.trash` | `trait Trash` (trash, restore); `object Trash`, the branch `TrashUntilGone` and the contracts; `TrashService` |
| `sharing.housekeeping` | `trait Housekeeping` (tidy); the branch `HousekeepingClearsOnlyTheEnded`, the contract, and the job on the store and the clock (`HousekeepingJob`, every minute) |
| `sharing.requests` | `trait AccessRequests` (ask, approve, decline, chase); the branch `AccessRequestsAreAsks` and the contracts; `AccessRequestsService` |
| `sharing.ownership` | `trait Ownership` (transfer); the branch `OwnersKeepTheirDocuments` and the contract; `OwnershipService` |
| `sharing.audit` | `trait Audit` (record); the branch `AuditTrail` (every share at every moment made by a logged request) and the contract |
| `sharing.notifications` | `trait Notifications` (announce), the mail server's boundary and model (`MailerKept`), the branch `NoticesFollowChanges`, and the delivery job (`DeliveryJob`: the outbox sent, retried with a schedule) |
| `sharing.time` | how long things last (`Lifetimes`: in force, open, gone, fixed with the clock); the clock's assumption; the service as a run of events (`Run`) and the deadlines over it (`Deadlines`) |
| `sharing.store` | `trait LibraryStore`, its model and assumption (`LibraryKept`); the memory store and the SQLite store |
| `sharing.http` | requests and answers; `SharingHttp.handleContract`, the proven handling of a request on the store; the HTTP codec and the server |
| `sharing` (`Knowledge.scala`) | the knowledge base: nodes, implementations, generators, the CLI |

## Running it

    bin/frflow sharing status                                 # the tree; exits 0 when every node is accepted and proven
    sbt "sharing/test"                                        # examples, store against its model, HTTP against an oracle
    sbt "sharing/runMain sharing.http.sharingServer 8091 library.db"
    sbt "sharing/runMain sharing.http.sharingServer 8091 library.db --fake-clock 1000000"   # time moves only by POST /clock

    curl "http://127.0.0.1:8091/access?person=bob&doc=q3-report"                 # {"access":"view"}
    curl -X POST -d '{"by":"ann","what":{"doc":"plan"},"with":{"team":"eng"},"level":"view"}' http://127.0.0.1:8091/share
    curl -X POST -d '{"by":"ann","doc":"plan","into":"q3"}' http://127.0.0.1:8091/move

With a fake clock, `POST /faults {"fail":[false,true]}` fails the next calls of the store and the mail server (a
request the store fails is answered 503 and changes nothing); `POST /housekeep`, `POST /deliver`, `GET /log`,
`GET /outbox`, `GET /requests` and `GET /mailbox` drive and show the rest.

People are named in requests: there is no sign-in. The server starts a new file with the demo library (`Demo.scala`).
