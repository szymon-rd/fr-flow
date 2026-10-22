package crm

/** The running write side: SaveWrite's code through service, on the store loaded from the database, one
  * write at a time. The code applies the write (WriteContract's code, its result checked) and stores the
  * rows about the written record through StoreEdits (read back and checked); it returns those rows.
  * WriteSideWiring governs this file, so a change to it is the developer's to review.
  */
def writeSide(db: Db): WriteCmd => CrmStore =
  val save = knowledge.service(saveWrite)(database.bind(db))
  cmd => db.synchronized(save(db.load(), cmd))
