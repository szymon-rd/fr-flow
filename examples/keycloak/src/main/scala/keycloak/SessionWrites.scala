package keycloak

/** Writes to the store: the adapter behind StoreKeepsState. What it stores is read back, and checked
  * against the assumption on every call.
  */
extension (db: SessionDb)
  /** Stores a request in the log and the state it led to; returns the state stored afterwards, read back. */
  def storeAfter(q: AuthRequest, after: ServerState): ServerState = db.synchronized {
    db.replaceWith(q, after)
    db.load()
  }
