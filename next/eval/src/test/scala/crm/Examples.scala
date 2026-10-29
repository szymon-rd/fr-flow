package crm

import frflow.*

// Today's examples, one class per node they were written on (owner §18). Those reading what the CRM holds give it,
// with the history that led to it and the clock: checked against the code in Scala only. The others give nothing,
// and are tried against the claims in Lean too. Today's examples of the expiry job, about the database's worlds,
// are runs on the database (crm's `PortSuite`).

private val acme = TenantId("acme")
private val globex = TenantId("globex")
private val ann = Account("ann@acme", acme)
private val gil = Account("gil@globex", globex)
private val acmeDeal = CrmRecord(1, acme, Kind.Deal, "Acme deal")
private val globexContact = CrmRecord(2, globex, Kind.Contact, "Globex contact")
private val acmeContact = CrmRecord(2, acme, Kind.Contact, "Acme contact")
private def adds(u: Account, r: CrmRecord): Event = Event.Wrote(WriteCmd(u, Change.Add(r)))
private def holding(rs: CrmRecord*): CrmStore = CrmStore(rs.toList, Nil, Nil)

class QueryExamples extends FrFlowExamples(knowledge):
  private val acmeContact3 = CrmRecord(3, acme, Kind.Contact, "Acme contact")
  private val stored = List(history := List(adds(ann, acmeDeal), adds(gil, globexContact), adds(ann, acmeContact3)),
    held := holding(acmeDeal, globexContact, acmeContact3))

  example("every company's contacts: the database does not filter by company, the read side does", stored*):
    fetch(ann, Search.OfKind(Kind.Contact)) is List(globexContact, acmeContact3)
  example("a record by its id", stored*):
    fetch(ann, Search.ById(1)) is List(acmeDeal)
  example("a stored record is never left out", stored*):
    (fetch(ann, Search.Everything) is List(acmeDeal)) is false

class ReadExamples extends FrFlowExamples(knowledge):
  private val two = List(history := List(adds(ann, acmeDeal), adds(gil, globexContact)),
    held := holding(acmeDeal, globexContact), clock := BigInt(0))
  private val sharedUntil100 = List(adds(gil, globexContact),
    Event.Wrote(WriteCmd(gil, Change.ShareWith(2, acme, Some(100)))))
  private val shared = CrmStore(List(globexContact), List(Share(2, acme)), List(Expiry(2, acme, 100)))
  private def at(now: Int) = List(history := sharedUntil100, held := shared, clock := BigInt(now))

  example("Ann lists everything she can see: the deal she added", two*):
    read(ann, Search.Everything) is List(acmeDeal)
  example("Globex's contact is not shared with Acme", two*):
    read(ann, Search.ById(2)) is Nil
  example("another company's record is never returned", two*):
    (read(ann, Search.ById(2)) is List(globexContact)) is false
  example("a record relabelled as Acme's is not a stored record", two*):
    (read(ann, Search.Everything) is List(CrmRecord(2, acme, Kind.Contact, "Globex contact"))) is false
  example("a search for contacts does not return deals", two*):
    (read(ann, Search.OfKind(Kind.Contact)) is List(acmeDeal)) is false
  example("Globex shared its contact with Acme until 100: at 50 Ann finds it by kind", at(50)*):
    read(ann, Search.OfKind(Kind.Contact)) is List(globexContact)
  example("at 150 the share has ended, though the expiry job has not run: Ann no longer finds the contact", at(150)*):
    read(ann, Search.OfKind(Kind.Contact)) is Nil
  example("a share past its time never shows the record", at(150)*):
    (read(ann, Search.OfKind(Kind.Contact)) is List(globexContact)) is false
  // Today's `acmeNeverSeesGlobex` (owner §40): an example, not a node.
  example("Someone at Acme never sees a Globex record that Globex did not share with Acme, whatever they search " +
      "for", history := List(adds(ann, acmeDeal), adds(gil, globexContact), adds(gil, CrmRecord(3, globex, Kind.Deal,
        "Globex deal")), Event.Wrote(WriteCmd(gil, Change.ShareWith(3, acme, None)))),
      held := CrmStore(List(acmeDeal, globexContact, CrmRecord(3, globex, Kind.Deal, "Globex deal")),
        List(Share(3, acme)), Nil), clock := BigInt(0)):
    read(ann, Search.Everything).forall(r => (r.tenant === globex) implies held.shares.contains(make[Share](r.id,
      acme))) is true

class DealExamples extends FrFlowExamples(knowledge):
  private val stored = List(history := List(adds(ann, acmeDeal), adds(ann, acmeContact)),
    held := holding(acmeDeal, acmeContact), clock := BigInt(0))

  example("Ann's deal search lists Acme's deal, not its contact", stored*):
    deals(ann, Search.Everything) is List(acmeDeal)
  example("a search for contacts finds no deal", stored*):
    deals(ann, Search.OfKind(Kind.Contact)) is Nil
  example("a contact is never listed as a deal", stored*):
    (deals(ann, Search.Everything) is List(acmeContact)) is false
  example("a deal Ann may see is never left out", stored*):
    (deals(ann, Search.Everything) is Nil) is false

private val acmeContact1 = CrmRecord(1, acme, Kind.Contact, "Acme contact")
private val globexDeal = CrmRecord(2, globex, Kind.Deal, "Globex deal")

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

class SaveExamples extends FrFlowExamples(knowledge):
  example("Ann's new contact is stored, and only its rows"):
    save(CrmStore(List(globexDeal), List(Share(2, acme)), Nil), WriteCmd(ann, Change.Add(acmeContact1))) is
      holding(acmeContact1)
  example("sharing until 100 stores the record's share and its expiry"):
    save(holding(acmeContact1), WriteCmd(ann, Change.ShareWith(1, globex, Some(100)))) is
      CrmStore(List(acmeContact1), List(Share(1, globex)), List(Expiry(1, globex, 100)))
  example("a write the database dropped is seen"):
    (save(holding(), WriteCmd(ann, Change.Add(acmeContact1))) is holding()) is false

class StoreExamples extends FrFlowExamples(knowledge):
  private val globexDeal2 = CrmRecord(2, globex, Kind.Deal, "Globex deal")
  example("the record and its share, not the other record"):
    storeRows(1, CrmStore(List(acmeDeal, globexDeal2), List(Share(1, globex)), Nil)) is
      CrmStore(List(acmeDeal), List(Share(1, globex)), Nil)
  example("nothing is held about record 3"):
    storeRows(3, holding(acmeDeal)) is holding()
  example("a share the database dropped is seen"):
    (storeRows(1, CrmStore(List(acmeDeal), List(Share(1, globex)), Nil)) is holding(acmeDeal)) is false

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
