package crm

/** The running read side: the registered implementation, every result checked against the contract
  * and the invariants it keeps. ReadSideWiring governs this file, so a change to it is the developer's
  * to review.
  */
def readSide(records: List[CrmRecord], shareTable: List[Share]): (Account, Search) => List[CrmRecord] =
  knowledge.service(readContract)(store.bind(records), shares.bind(shareTable))

/** The deals screen: DealSearch's code, calling the read side above for its records. */
def dealSide(records: List[CrmRecord], shareTable: List[Share]): (Account, Search) => List[CrmRecord] =
  knowledge.service(dealSearch)(store.bind(records), shares.bind(shareTable))
