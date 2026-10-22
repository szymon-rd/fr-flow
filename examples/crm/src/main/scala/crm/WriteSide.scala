package crm

/** The running write side: the registered implementation, every new store checked against
  * WriteContract. WriteSideWiring governs this file, so a change to it is the developer's to review.
  */
def writeSide(): (CrmStore, WriteCmd) => CrmStore =
  knowledge.service(writeContract)()

/** A write on the database: the stored records and shares, the proven step, stored back in one go. */
def writeTo(db: Db, cmd: WriteCmd): CrmStore = db.synchronized {
  val t = writeSide()(db.load(), cmd)
  db.save(t)
  t
}
