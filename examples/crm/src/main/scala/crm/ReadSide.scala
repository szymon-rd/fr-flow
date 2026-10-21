package crm

/** The running read side: the registered implementation, every result checked against the contract.
  * It lives in the implementation's package, so ReadContract governs it and a change is reviewed.
  */
def readSide(records: List[CrmRecord], shareTable: List[Share]): (Account, Search) => List[CrmRecord] =
  knowledge.service(readContract)(store.bind(records), shares.bind(shareTable))
