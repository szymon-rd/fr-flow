package crm

import frflow.*

// Two of crm's claims in the owner's forms: `saveWrite`, which relates its Definition to another applied to the
// same inputs (the one on the left of its equation is the one it reads as a call of); and `expiryJob`, a claim about a
// program, a run from the world before.

final case class CrmStore(rows: List[BigInt]) derives LeanType
final case class WriteCmd(about: BigInt, row: BigInt) derives LeanType
enum Event derives LeanType:
  case Expired(at: BigInt)
final case class Tables(store: CrmStore, events: List[Event]) derives LeanType

val write = Definition[(CrmStore, WriteCmd) => CrmStore]("a write applied to the store")
val save = Definition[(CrmStore, WriteCmd) => CrmStore]("the write side: a write stored, its record's rows read back")
val expire = Definition[(CrmStore, BigInt) => CrmStore]("the store with what has expired at a moment removed")
val runExpiry = Definition[BigInt => Program[CrmStore]]("a run of the expiry job at a moment")
val databaseModel = ModelState[Tables]("the database's tables")

val about = define { (w: Term[WriteCmd]) => w.about }
val aboutRecord = define { (s: Term[CrmStore], r: Term[BigInt]) => make[CrmStore](s.rows.filter(x => x === r)) }
val sameRows = define { (a: Term[CrmStore], b: Term[CrmStore]) => a.rows === b.rows }
val noEvents: Term[List[Event]] = Nil

val saveWrite = Node.claim("A write is stored, and the rows about its record are returned as read back.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => save(s, w) === aboutRecord(write(s, w), about(w))))

val expiryJob = Node.claim(
    "A run of the expiry job removes what has expired, logs it, and returns the store.")(
  forall((now: Term[BigInt], before: Term[World]) =>
    runExpiry(now).from(before) { (result, after) =>
      sameRows(databaseModel.in(after).store, expire(databaseModel.in(before).store, now)) &&
        databaseModel.in(after).events === databaseModel.in(before).events ++ (make[Event.Expired](now) :: noEvents) &&
        result === expire(databaseModel.in(before).store, now) }))
