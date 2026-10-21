package crm

import frflow.*

// ============================================================================
// Root: tenant isolation, generic
// ============================================================================

val Tenant = Opaque("Tenant", "a company that uses the CRM")
val User   = Opaque("User", "a person who works for a company")
val Record = Opaque("Record", "a contact or a deal kept in the CRM")

val tenantOf   = Param[User.T => Tenant.T]("tenantOf", "the company a user works for")
val owner      = Param[Record.T => Tenant.T]("owner", "the company a record belongs to")
val sharedWith = Param[(Record.T, Tenant.T) => Boolean]("sharedWith", "whether the record's company shared it with the given company")

/** A user may see a record of their own company, or one shared with it. */
val visible = define { (u: User.T, r: Record.T) => owner(r) == tenantOf(u) || sharedWith(r, tenantOf(u)) }

/** Model: whom the system shows which records. */
val isolation = Node.root[(User.T, Record.T) => Boolean](
  "TenantIsolation",
  "A user sees a record only if it belongs to their company or was shared with their company.",
  why = "Isolation between companies is what the idea says must hold. Companies, users, records and sharing are left open."
)(shows => forall((u: User.T, r: Record.T) => shows(u, r) ==> visible(u, r)))

// ============================================================================
// Users see records only through queries
// ============================================================================

val Query = Opaque("Query", "a search a user runs")

/** Model: what a query returns to a user. */
val readApi = isolation.refine[(User.T, Query.T) => List[Record.T]](
  "ReadApi",
  "Records are shown only as query results, and a query returns only records the user may see.",
  why = "Users find records by searching, so what a user sees is what their queries return. abs: a user is shown a record when some query of theirs returns it."
)(
  abs  = run => (u, r) => exists((q: Query.T) => run(u, q).contains(r)),
  spec = run => forall((u: User.T, q: Query.T) => run(u, q).forall(r => visible(u, r)))
)

// ============================================================================
// Instantiation: the concrete CRM domain
// ============================================================================

final case class TenantId(value: String)
final case class Account(email: String, tenant: TenantId)

enum Kind:
  case Contact, Deal

final case class CrmRecord(id: Long, tenant: TenantId, kind: Kind, title: String)
final case class Share(record: Long, to: TenantId)

enum Search:
  case ById(id: Long)
  case OfKind(kind: Kind)
  case Everything

val shares = Param[List[Share]]("shares", "the share table as stored when the search runs")

val accounts = readApi.instantiate[(Account, Search) => List[CrmRecord]](
  "Accounts",
  "Users are accounts of a company, records are contacts and deals, and sharing is a table of shares.",
  why = "A record belongs to the company stored on it, and a user to the company of their account. This trusts the record, so ReadContract requires returned records to be the stored ones; it also trusts the account, which authentication provides (not modelled)."
)(
  Tenant     := of[TenantId],
  User       := of[Account],
  Record     := of[CrmRecord],
  Query      := of[Search],
  tenantOf   := ((a: Account) => a.tenant),
  owner      := ((r: CrmRecord) => r.tenant),
  sharedWith := ((r: CrmRecord, t: TenantId) => shares.value.contains(Share(r.id, t)))
)

// ============================================================================
// Contract for implementations
// ============================================================================

val store = Param[List[CrmRecord]]("store", "the records as stored when the search runs")

val readContract = accounts.contract[Account, Search, List[CrmRecord]](
  "ReadContract",
  "A search returns stored records only, each of the user's company or shared with it.",
  why = "Accounts, stated for one call. A returned record must be one of the stored records, so an implementation cannot relabel another company's record as the user's."
)((user, query, result) => result.forall(r => store.value.contains(r) && (r.tenant == user.tenant || shares.value.contains(Share(r.id, user.tenant)))))
  .examples(
    store.bind(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"))),
    shares.bind(Nil))(
    expect(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "Ann lists everything she can see: Acme's deal"),
    expect(Account("ann@acme", TenantId("acme")), Search.ById(2), Nil, "Globex's contact is not shared with Acme"),
    reject(Account("ann@acme", TenantId("acme")), Search.ById(2), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "another company's record is never returned"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(2, TenantId("acme"), Kind.Contact, "Globex contact")),
      "a record relabelled as Acme's is not a stored record"))
  .examples(
    store.bind(List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"))),
    shares.bind(List(Share(2, TenantId("acme")))))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "Globex shared its contact with Acme, so Ann finds it by kind"))

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(isolation, readApi, accounts, readContract)
  .implement(readContract)(InMemoryCrm(store.value, shares.value).search)

/** The running read side: the registered implementation, every result checked against the contract. */
def readSide(records: List[CrmRecord], shareTable: List[Share]): (Account, Search) => List[CrmRecord] =
  knowledge.service(readContract)(store.bind(records), shares.bind(shareTable))

@main def crmCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/crm"))
