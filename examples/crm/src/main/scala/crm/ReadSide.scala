package crm

/** The running read side: ReadContract's code on the database, every result checked (its
  * `checkedBy`: each record matches the search and the reader may see it). ReadSideWiring governs
  * this file, so a change to it is the developer's to review.
  */
def readSide(db: Db): (Account, Search) => List[CrmRecord] =
  knowledge.service(readContract)(store.bind(db.allRecords()), shares.bind(db.shares()), database.bind(db))

/** The deals screen: DealSearch's code, calling the read side above for its records. */
def dealSide(db: Db): (Account, Search) => List[CrmRecord] =
  knowledge.service(dealSearch)(store.bind(db.allRecords()), shares.bind(db.shares()), database.bind(db))
