package crm

/** The running read side: the records screen (ReadContract's code on the database) and the sales screen
  * (DealSearch's code, calling the records screen), every result checked (their `checkedBy` and the
  * invariant they keep). ReadSideWiring governs this file, so a change to it is the developer's to review.
  */
def readSide(db: Db): (Account, Search) => List[CrmRecord] =
  knowledge.service(readContract)(store.bind(db.allRecords()), shares.bind(db.shares()), database.bind(db))

/** The sales screen: DealSearch's code, calling the records screen above for its records. */
def dealSide(db: Db): (Account, Search) => List[CrmRecord] =
  knowledge.service(dealSearch)(store.bind(db.allRecords()), shares.bind(db.shares()), database.bind(db))
