package frflow.reference

import _root_.crm.*

/** crm's seeded bugs, as `CrmSuite` seeds them. */
object CrmBugs:
  private val acme = TenantId("acme")
  private val globex = TenantId("globex")
  private val ann = Account("ann@acme", acme)
  private val records = List(CrmRecord(1, acme, Kind.Contact, "Ann's contact"),
    CrmRecord(2, globex, Kind.Deal, "Globex deal"), CrmRecord(3, globex, Kind.Contact, "Shared contact"))
  private val shareTable = List(Share(3, acme))
  private def db() = Db.of(records, shareTable)
  private def reading(d: Db) = List(store.bind(d.allRecords()), shares.bind(d.shares()), expiries.bind(d.expiries()),
    history.bind(d.events()), clock.bind(BigInt(0)), database.bind(d))
  private val world = "records 1 (acme), 2 and 3 (globex), 3 shared with acme"

  def all: List[Seeded] = List(leaky, relabel, whereDropped, careless, dropping, limited, ModelBug.leakyStore)

  private def leaky: Seeded =
    val leaks: (Account, Search) => List[CrmRecord] = (_, _) => records
    val kb = knowledge.implementTested(readContract)(leaks)
    Seeded("leaky read", inTable = true, "readContract implemented by (_, _) => every record, another company's too",
      "CrmSuite: an implementation that leaks another company's records is stopped by its check, on every call",
      Stops.onCall(s"read(ann@acme, Everything), $world")(
        kb.service(readContract)(reading(db())*)(ann, Search.Everything)) ++
        Stops.examples(kb, readContract) ++ Stops.generated(kb, readContract))

  private def relabel: Seeded =
    val relabels: (Account, Search) => List[CrmRecord] = (u, _) => store.value.map(_.copy(tenant = u.tenant))
    val kb = knowledge.implementTested(readContract)(relabels)
    Seeded("relabel read", inTable = true,
      "readContract implemented by every record relabelled as the user's company's",
      "CrmSuite: an implementation that relabels another company's records fails its examples (the cheap check sees " +
        "the label only)",
      Stops.examples(kb, readContract) ++ Stops.generated(kb, readContract))

  private def whereDropped: Seeded =
    val kb = knowledge.implementProven(recordsByQuery)(storedMatching, (u, q) => database.value.allRecords())
    Seeded("SQL WHERE dropped", inTable = true,
      "recordsByQuery's SQL beside storedMatching returns every record (its WHERE dropped)",
      "CrmSuite: a seeded SQL bug (the search's WHERE dropped) is stopped by the port's check; the proofs still hold",
      Stops.onCall(s"read(ann@acme, OfKind(Deal)), $world")(
        kb.service(readContract)(reading(db())*)(ann, Search.OfKind(Kind.Deal))) ++
        Stops.generated(kb, recordsByQuery) ++ Stops.examples(kb, recordsByQuery))

  private def careless: Seeded =
    val drops: (CrmStore, WriteCmd) => CrmStore = (s, _) => s.copy(records = s.records.filter(_.tenant == acme))
    val kb = knowledge.implementTested(writeContract)(drops)
    Seeded("careless write", inTable = true, "writeContract implemented by dropping every record not of acme",
      "CrmSuite: a write changes only what its author's company may change, and the write side checks it",
      Stops.onCall(s"write(store, ann@acme: Unshare(1, globex)), $world") {
        kb.service(writeContract)()(CrmStore(records, shareTable, Nil), WriteCmd(ann, Change.Unshare(1, globex)))
      } ++ Stops.generated(kb, writeContract) ++ Stops.examples(kb, writeContract))

  private def dropping: Seeded =
    val kb = knowledge.implementProven(storeEdits)(storedAbout, (id, t) => CrmStore(Nil, Nil, Nil))
    Seeded("dropping database", inTable = true,
      "storeEdits' code beside storedAbout stores nothing: (id, t) => CrmStore(Nil, Nil, Nil)",
      "CrmSuite: a database that drops a write is seen on the call: StoreEdits reads the rows back, under the write " +
        "side too",
      Stops.onCall(s"storeEdits(1, CrmStore(records, Nil, Nil)), $world")(
        kb.service(storeEdits)(database.bind(db()))(BigInt(1), CrmStore(records, Nil, Nil))) ++
        Stops.onCall(s"saveWrite(load(), ann@acme: Add(4, acme, Deal)), $world") {
          val d = db()
          val add = WriteCmd(ann, Change.Add(CrmRecord(4, acme, Kind.Deal, "New deal")))
          kb.service(saveWrite)(database.bind(d))(d.load(), add)
        } ++ Stops.generated(kb, storeEdits) ++ Stops.examples(kb, storeEdits))

  private def limited: Seeded =
    val kb = knowledge.implementProven(recordsByQuery)(storedMatching,
      (u, q) => database.value.recordsMatching(q).take(2))
    Seeded("SQL with LIMIT 2", inTable = false, "recordsByQuery's SQL returns at most two rows: right on the examples",
      "CrmSuite: SQL that is right on the examples but drops rows on other inputs is found by the generated cases",
      Stops.examples(kb, recordsByQuery) ++ Stops.generated(kb, recordsByQuery))
