# rebac

A Zanzibar-style authorization service built with FrFlow. What it is for is in [IDEA.md](IDEA.md); how it is refined,
proven and decided is in `src/main/scala/rebac` and `bin/frflow rebac status`.

## Running it

    sbt "rebac/runMain rebac.rebacServer 8090"

    curl -X POST 'http://127.0.0.1:8090/write?tuple=doc:readme%23viewer@user:ann'     # → 1, the new version
    curl 'http://127.0.0.1:8090/check?tuple=doc:readme%23viewer@user:ann'             # → yes (Rebac-Version: 1)
    curl 'http://127.0.0.1:8090/check?tuple=doc:readme%23viewer@user:ann&at=0'        # → no
    curl -X POST 'http://127.0.0.1:8090/delete?tuple=doc:readme%23viewer@user:ann'    # → 2

A malformed tuple, a relation the schema does not declare, an empty user id or an `at` that is not a version from 0 to
the latest is refused with 400 and the reason. A request is given 10 s on a pool of 8 workers (503 past that); an
internal error is answered 500 and logged with the request.

## Out of scope

- **Writes are not authenticated.** Anyone who can reach the port can write and delete tuples. The server listens on
  127.0.0.1 only; put it behind something that authenticates before exposing it.
- **No persistence.** Tuples and the cache are kept in memory; a restart starts at version 0 with no tuples.
- One process: no replication, no consistency tokens beyond the version number.

The server prints the first two at startup.
