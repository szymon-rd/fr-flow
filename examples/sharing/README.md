# Sharing

People keep documents in folders and share them with people or teams, to view or to edit. The idea is in
[IDEA.md](IDEA.md); the root, `AccessFollowsShares` (`Purpose.scala`), says the shares decide access exactly and
only editors change shares or move documents.

## Where things are

| Package | What is in it |
|---|---|
| `sharing.domain` | the data: people, teams, documents, folders, shares, the library |
| `sharing` (`Purpose.scala`) | the meaning (Reach, Cover, Permission) and the root |
| `sharing.service` | `trait Sharing`, the service; `object Sharing`, one contract per method, each with its proven code; `SharingService` runs it |
| `sharing.store` | `trait LibraryStore`, its model and assumption (`LibraryKept`); the memory store and the SQLite store |
| `sharing.http` | requests and answers; `SharingHttp.handleContract`, the proven handling of a request on the store; the HTTP codec and the server |
| `sharing` (`Knowledge.scala`) | the knowledge base: nodes, implementations, generators, the CLI |

## Running it

    bin/frflow sharing status                                 # the tree; exits 0 when every node is accepted and proven
    sbt "sharing/test"                                        # examples, store against its model, HTTP against an oracle
    sbt "sharing/runMain sharing.http.sharingServer 8091 library.db"

    curl "http://127.0.0.1:8091/access?person=bob&doc=q3-report"                 # {"access":"view"}
    curl -X POST -d '{"by":"ann","what":{"doc":"plan"},"with":{"team":"eng"},"level":"view"}' http://127.0.0.1:8091/share
    curl -X POST -d '{"by":"ann","doc":"plan","into":"q3"}' http://127.0.0.1:8091/move

People are named in requests: there is no sign-in. The server starts a new file with the demo library (`Demo.scala`).
