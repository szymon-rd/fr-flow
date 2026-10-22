package crm

/** The running read side: the records screen (ReadContract's code on the database) and the sales screen
  * (DealSearch's code, calling the records screen), every result checked (their `checkedBy` and the
  * invariant they keep). The tables are what the event log led to (CrmRun): only the write side and the
  * expiry job change them. ReadSideWiring governs this file, so a change to it is the developer's to review.
  */
def readSide(db: Db): (Account, Search) => List[CrmRecord] =
  knowledge.service(readContract)(bindings(db)*)

/** The sales screen: DealSearch's code, calling the records screen above for its records. */
def dealSide(db: Db): (Account, Search) => List[CrmRecord] =
  knowledge.service(dealSearch)(bindings(db)*)

/** What a search reads: the tables as stored, the event log, and the clock (in seconds) when it runs. */
private def bindings(db: Db) = List(store.bind(db.allRecords()), shares.bind(db.shares()), expiries.bind(db.expiries()),
  history.bind(db.events()), clock.bind(BigInt(System.currentTimeMillis / 1000)), database.bind(db))
