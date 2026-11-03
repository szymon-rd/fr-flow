package crm

import frflow.*

// Today's examples, one list or class per node they were written on (owner §18). Those of a write and of the expiry
// job's store, functions, are examples, tried against the claims in Lean too. Those of the database's search, the
// screens, the write side and the database's storing were given what the CRM holds, its history and the clock; those
// are the World's now (owner §45 D) and an example reads no world (2.10), so each is a run of the code on a database
// holding them, at a time, in production's interpreter (crm's `PortSuite`), as are today's examples of the expiry
// job's runs and the root's expectation.

private val acme = TenantId("acme")
private val globex = TenantId("globex")
private val ann = Account("ann@acme", acme)
private val gil = Account("gil@globex", globex)
private val acmeDeal = CrmRecord(1, acme, Kind.Deal, "Acme deal")
private val globexContact = CrmRecord(2, globex, Kind.Contact, "Globex contact")
private val acmeContact = CrmRecord(2, acme, Kind.Contact, "Acme contact")
private val acmeContact1 = CrmRecord(1, acme, Kind.Contact, "Acme contact")
private val acmeContact3 = CrmRecord(3, acme, Kind.Contact, "Acme contact")
private val globexDeal = CrmRecord(2, globex, Kind.Deal, "Globex deal")
private def adds(u: Account, r: CrmRecord): Event = Event.Wrote(WriteCmd(u, Change.Add(r)))
private def holding(rs: CrmRecord*): CrmStore = CrmStore(rs.toList, Nil, Nil)

/** One of today's examples of a run: what it says, the tables and the time it runs on, the run's inputs, what it
  * gives, and whether it gives that (`holds`) or never does.
  */
final case class RunExample[I, O](says: String, from: (Tables, BigInt), inputs: I, gives: O, holds: Boolean = true)

private val three = Tables(holding(acmeDeal, globexContact, acmeContact3),
  List(adds(ann, acmeDeal), adds(gil, globexContact), adds(ann, acmeContact3))) -> BigInt(0)

/** Today's examples of the database's search. */
val queries: List[RunExample[(Account, Search), List[CrmRecord]]] = List(
  RunExample("every company's contacts: the database does not filter by company, the read side does", three,
    (ann, Search.OfKind(Kind.Contact)), List(globexContact, acmeContact3)),
  RunExample("a record by its id", three, (ann, Search.ById(1)), List(acmeDeal)),
  RunExample("a stored record is never left out", three, (ann, Search.Everything), List(acmeDeal), holds = false))

private val two = Tables(holding(acmeDeal, globexContact), List(adds(ann, acmeDeal), adds(gil, globexContact)))
private val sharedUntil100 = Tables(CrmStore(List(globexContact), List(Share(2, acme)), List(Expiry(2, acme, 100))),
  List(adds(gil, globexContact), Event.Wrote(WriteCmd(gil, Change.ShareWith(2, acme, Some(100))))))

/** Today's examples of the records screen. */
val reads: List[RunExample[(Account, Search), List[CrmRecord]]] = List(
  RunExample("Ann lists everything she can see: the deal she added", two -> 0, (ann, Search.Everything),
    List(acmeDeal)),
  RunExample("Globex's contact is not shared with Acme", two -> 0, (ann, Search.ById(2)), Nil),
  RunExample("another company's record is never returned", two -> 0, (ann, Search.ById(2)), List(globexContact),
    holds = false),
  RunExample("a record relabelled as Acme's is not a stored record", two -> 0, (ann, Search.Everything),
    List(CrmRecord(2, acme, Kind.Contact, "Globex contact")), holds = false),
  RunExample("a search for contacts does not return deals", two -> 0, (ann, Search.OfKind(Kind.Contact)),
    List(acmeDeal), holds = false),
  RunExample("Globex shared its contact with Acme until 100: at 50 Ann finds it by kind", sharedUntil100 -> 50,
    (ann, Search.OfKind(Kind.Contact)), List(globexContact)),
  RunExample("at 150 the share has ended, though the expiry job has not run: Ann no longer finds the contact",
    sharedUntil100 -> 150, (ann, Search.OfKind(Kind.Contact)), Nil),
  RunExample("a share past its time never shows the record", sharedUntil100 -> 150,
    (ann, Search.OfKind(Kind.Contact)), List(globexContact), holds = false))

/** Today's `acmeNeverSeesGlobex` (owner §40), an example, not a node: on these tables, every Globex record Ann's
  * search for everything returns is one Globex shared with Acme.
  */
val acmeNeverSeesGlobex: (Tables, BigInt) = Tables(CrmStore(List(acmeDeal, globexContact,
  CrmRecord(3, globex, Kind.Deal, "Globex deal")), List(Share(3, acme)), Nil), List(adds(ann, acmeDeal),
  adds(gil, globexContact), adds(gil, CrmRecord(3, globex, Kind.Deal, "Globex deal")),
  Event.Wrote(WriteCmd(gil, Change.ShareWith(3, acme, None))))) -> 0

private val dealAndContact = Tables(holding(acmeDeal, acmeContact), List(adds(ann, acmeDeal), adds(ann, acmeContact)))

/** Today's examples of the sales screen. */
val dealRuns: List[RunExample[(Account, Search), List[CrmRecord]]] = List(
  RunExample("Ann's deal search lists Acme's deal, not its contact", dealAndContact -> 0, (ann, Search.Everything),
    List(acmeDeal)),
  RunExample("a search for contacts finds no deal", dealAndContact -> 0, (ann, Search.OfKind(Kind.Contact)), Nil),
  RunExample("a contact is never listed as a deal", dealAndContact -> 0, (ann, Search.Everything), List(acmeContact),
    holds = false),
  RunExample("a deal Ann may see is never left out", dealAndContact -> 0, (ann, Search.Everything), Nil,
    holds = false))

/** Today's examples of the write side, each on the database holding the store given: the rows it returns. */
val saves: List[RunExample[WriteCmd, CrmStore]] = List(
  RunExample("Ann's new contact is stored, and only its rows", Tables(CrmStore(List(globexDeal), List(Share(2, acme)),
    Nil), Nil) -> 0, WriteCmd(ann, Change.Add(acmeContact1)), holding(acmeContact1)),
  RunExample("sharing until 100 stores the record's share and its expiry", Tables(holding(acmeContact1), Nil) -> 0,
    WriteCmd(ann, Change.ShareWith(1, globex, Some(100))),
    CrmStore(List(acmeContact1), List(Share(1, globex)), List(Expiry(1, globex, 100)))),
  RunExample("a write the database dropped is seen", Tables(holding(), Nil) -> 0,
    WriteCmd(ann, Change.Add(acmeContact1)), holding(), holds = false))

private val empty = Tables(holding(), Nil) -> BigInt(0)

/** Today's examples of the database storing the rows about one record, each on the empty database: what it holds
  * after.
  */
val stores: List[RunExample[(BigInt, CrmStore), CrmStore]] = List(
  RunExample("the record and its share, not the other record", empty,
    (1, CrmStore(List(acmeDeal, globexDeal), List(Share(1, globex)), Nil)),
    CrmStore(List(acmeDeal), List(Share(1, globex)), Nil)),
  RunExample("nothing is held about record 3", empty, (3, holding(acmeDeal)), holding()),
  RunExample("a share the database dropped is seen", empty, (1, CrmStore(List(acmeDeal), List(Share(1, globex)),
    Nil)), holding(acmeDeal), holds = false))

class WriteExamples extends FrFlowExamples(knowledge):
  example("Ann adds a contact of Acme's"):
    write(holding(), WriteCmd(ann, Change.Add(acmeContact1))) is holding(acmeContact1)
  example("Ann shares Acme's contact with Globex"):
    write(holding(acmeContact1, globexDeal), WriteCmd(ann, Change.ShareWith(1, globex, None))) is
      CrmStore(List(acmeContact1, globexDeal), List(Share(1, globex)), Nil)
  example("Ann shares it with Globex until 100"):
    write(holding(acmeContact1), WriteCmd(ann, Change.ShareWith(1, globex, Some(100)))) is
      CrmStore(List(acmeContact1), List(Share(1, globex)), List(Expiry(1, globex, 100)))
  example("Ann cannot share Globex's deal with herself"):
    (write(holding(acmeContact1, globexDeal), WriteCmd(ann, Change.ShareWith(2, acme, None))) is
      CrmStore(List(acmeContact1, globexDeal), List(Share(2, acme)), Nil)) is false
  example("a write never removes another company's record"):
    (write(holding(globexDeal), WriteCmd(ann, Change.Add(acmeContact1))) is holding()) is false
  example("a record with a taken id is never added beside it"):
    (write(holding(acmeContact1), WriteCmd(ann, Change.Add(acmeDeal))) is holding(acmeContact1, acmeDeal)) is false

class ExpireExamples extends FrFlowExamples(knowledge):
  private val until100 = CrmStore(List(acmeDeal), List(Share(1, globex), Share(1, TenantId("initech"))),
    List(Expiry(1, globex, 100)))
  private val globexOnly = CrmStore(List(acmeDeal), List(Share(1, globex)), List(Expiry(1, globex, 100)))
  example("Globex's share ended at 100; Initech's stays"):
    expire(until100, 150) is CrmStore(List(acmeDeal), List(Share(1, TenantId("initech"))), Nil)
  example("before 100 nothing ends"):
    expire(globexOnly, 50) is globexOnly
  example("a share that has not ended is never removed"):
    (expire(until100, 150) is holding(acmeDeal)) is false
  example("a run never removes a record"):
    (expire(globexOnly, 150) is holding()) is false
