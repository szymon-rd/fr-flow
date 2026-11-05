package crm

/** What the root is expected to give, on one history (owner §18): today's example, which reads the history and the
  * clock, the World's now (owner §45 D), so a run of the records screen on the tables the history left, at each time
  * (crm's `PortSuite`). When Ann at Acme has added a contact, and Gil at Globex a deal he shared with Acme until 100:
  * at 50 Ann finds both, at 150 only her contact, and Gil never finds Ann's contact.
  */
object ExpectationsExamples:
  val ann: Account = Account("ann@acme", TenantId("acme"))
  val gil: Account = Account("gil@globex", TenantId("globex"))
  val annContact: CrmRecord = CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")
  val gilDeal: CrmRecord = CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")

  /** The history, and the tables it left. */
  val history: List[Event] = List(Event.Wrote(WriteCmd(ann, Change.Add(annContact))),
    Event.Wrote(WriteCmd(gil, Change.Add(gilDeal))),
    Event.Wrote(WriteCmd(gil, Change.ShareWith(2, TenantId("acme"), Some(100)))))
  val tables: Tables = History.tables(history)

  /** Who searches for everything at what time, and what they find: Ann at 50 and at 150, Gil at 50. */
  val expected: List[(Account, BigInt, List[CrmRecord])] =
    List((ann, 50, List(annContact, gilDeal)), (ann, 150, List(annContact)), (gil, 50, List(gilDeal)))
