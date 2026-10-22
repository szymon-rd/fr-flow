package crm

/** The running write side: the registered implementation, every new store checked against
  * WriteContract, and the written record's rows stored through StoreEdits (read back and checked).
  * WriteSideWiring governs this file, so a change to it is the developer's to review.
  */
def writeSide(db: Db): WriteCmd => CrmStore =
  val (write, store) = (knowledge.service(writeContract)(), knowledge.service(storeEdits)(database.bind(db)))
  cmd => db.synchronized {
    val t = write(db.load(), cmd)
    // WriteContract: a write changes nothing about other records than its own.
    store(about.fn(cmd), t)
    t
  }
