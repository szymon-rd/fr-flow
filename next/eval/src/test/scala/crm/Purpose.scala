package crm

import frflow.*

// Crm's nodes in the three kinds (owner §15), each named as today's. The purpose's words are Declarations; today's
// definition nodes are claims, one equation each (a node that fixed two words is two claims); its `.expects` are
// claims the root refines (features.md, note 16); what the CRM holds now is a provided Definition, assumed to be what
// its history led to. Companies are `TenantId`s, users `Account`s, records `CrmRecord`s, queries `Ask`s.

// ============================================================================
// The domain: companies, records, shares, searches, writes, the expiry job
// ============================================================================

final case class TenantId(value: String) derives LeanType
final case class Account(email: String, tenant: TenantId) derives LeanType

enum Kind derives LeanType:
  case Contact, Deal

final case class CrmRecord(id: BigInt, tenant: TenantId, kind: Kind, title: String) derives LeanType
final case class Share(record: BigInt, to: TenantId) derives LeanType

/** Until when a share holds (a time in seconds); a share with none holds until it is unshared. */
final case class Expiry(record: BigInt, to: TenantId, until: BigInt) derives LeanType

enum Search derives LeanType:
  case ById(id: BigInt)
  case OfKind(kind: Kind)
  case Everything

enum Screen derives LeanType:
  case Records, Sales

/** A search, on a screen: the records screen, or the sales screen (deals only). */
final case class Ask(screen: Screen, search: Search) derives LeanType

final case class CrmStore(records: List[CrmRecord], shares: List[Share], expiries: List[Expiry]) derives LeanType

enum Change derives LeanType:
  case Add(record: CrmRecord)
  case ShareWith(record: BigInt, to: TenantId, until: Option[BigInt])
  case Unshare(record: BigInt, to: TenantId)

final case class WriteCmd(by: Account, change: Change) derives LeanType

/** What changes the store: a user's write, or a run of the expiry job at a time. */
enum Event derives LeanType:
  case Wrote(cmd: WriteCmd)
  case Expired(now: BigInt)

/** A share as a user asked it: of the record with that id, with a company, until a time or for good. */
final case class Grant(record: BigInt, to: TenantId, until: Option[BigInt]) derives LeanType

/** What users have asked of the CRM, as far as their companies may ask it: the records added, and the shares given
  * and not since unshared or ended.
  */
final case class Asked(records: List[CrmRecord], grants: List[Grant]) derives LeanType

// ============================================================================
// The purpose, in the most general terms
// ============================================================================

val companyOf = Declaration[Account => TenantId]("the company a user works for")
val owner = Declaration[CrmRecord => TenantId]("the company a record belongs to")
val sharedWith = Declaration[(CrmRecord, TenantId) => Boolean](
  "whether the record's company has shared it with the company, and that share holds now")
val asksFor = Declaration[(Ask, CrmRecord) => Boolean]("whether the record is one the search asks for")
val finds = Declaration[(Account, Ask, CrmRecord) => Boolean]("whether the user's search, run now, returns the record")
val added = Declaration[(TenantId, CrmRecord) => Boolean](
  "whether a user of the company has added the record to the CRM, for that company")

// What the CRM holds now, its history, the clock
val history = Definition[List[Event]]("the CRM's history since it started empty: every write the write side saved " +
  "and every run of the expiry job, in order (its event log)")
val held = Definition[CrmStore]("the records, shares and expiries the CRM holds now")
val clock = Definition[BigInt]("the time now, in seconds, by the server's clock: when a search runs")

// The operations: what the system does
val read = Definition[(Account, Search) => List[CrmRecord]]("the records screen: the records a user's search returns")
val deals = Definition[(Account, Search) => List[CrmRecord]]("the sales screen: the deals a user's search returns")
val fetch = Definition[(Account, Search) => List[CrmRecord]](
  "the database's answer to a search: the stored records, of every company, that match it")
val write = Definition[(CrmStore, WriteCmd) => CrmStore]("a write applied to a store: the store it leads to")
val save = Definition[(CrmStore, WriteCmd) => CrmStore]("the write side: a write applied to the store the " +
  "database holds, the rows about its record stored; it returns those rows as read back")
val storeRows = Definition[(BigInt, CrmStore) => CrmStore]("the database storing what a store holds about one " +
  "record in place of what it held about it; it returns the rows about the record, read back")
val expire = Definition[(CrmStore, BigInt) => CrmStore](
  "a run of the expiry job at a time (in seconds) on a store: the store it leads to")
val runExpiry = Definition[BigInt => Program[CrmStore]](
  "a run of the expiry job at a time (in seconds), on the database: the store it computes; the database holds it after")
