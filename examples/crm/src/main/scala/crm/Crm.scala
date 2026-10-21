package crm

import frflow.*

// ============================================================================
// Root: tenant isolation, generic
// ============================================================================

val Tenant = Opaque("Tenant")
val User   = Opaque("User")
val Record = Opaque("Record")

val tenantOf   = Param[User.T => Tenant.T]("tenantOf")
val owner      = Param[Record.T => Tenant.T]("owner")
val sharedWith = Param[(Record.T, Tenant.T) => Boolean]("sharedWith")

/** A user may see a record of their own company, or one shared with it. */
val visible = define { (u: User.T, r: Record.T) => owner(r) == tenantOf(u) || sharedWith(r, tenantOf(u)) }

/** Model: whom the system shows which records. */
val isolation = Node.root[(User.T, Record.T) => Boolean](
  "TenantIsolation",
  "A user sees a record only if it belongs to their company or was shared with their company."
)(shows => forall((u: User.T, r: Record.T) => shows(u, r) ==> visible(u, r)))

// ============================================================================
// Users see records only through queries
// ============================================================================

val Query = Opaque("Query")

/** Model: what a query returns to a user. */
val readApi = isolation.refine[(User.T, Query.T) => List[Record.T]](
  "ReadApi",
  "Records are shown only as query results, and a query returns only records the user may see."
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

val shares = Param[List[Share]]("shares")

val accounts = readApi.instantiate[(Account, Search) => List[CrmRecord]](
  "Accounts",
  "Users are accounts of a company, records are contacts and deals, and sharing is a table of shares."
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

val readContract = accounts.contract[Account, Search, List[CrmRecord]](
  "ReadContract",
  "A search returns only records of the user's company or shared with it."
)((user, query, result) => result.forall(r => r.tenant == user.tenant || shares.value.contains(Share(r.id, user.tenant))))

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(isolation, readApi, accounts, readContract)

// ============================================================================
// Implementation: plain Scala, attached to the contract
// ============================================================================

final class InMemoryCrm(records: List[CrmRecord], shareTable: List[Share]):
  def search(user: Account, query: Search): List[CrmRecord] =
    val sharedIds = shareTable.filter(_.to == user.tenant).map(_.record).toSet
    records
      .filter(r => r.tenant == user.tenant || sharedIds(r.id))
      .filter(r => query match
        case Search.ById(id)   => r.id == id
        case Search.OfKind(k)  => r.kind == k
        case Search.Everything => true)

/** The running read side: the implementation, with every result checked against the contract. */
def readSide(records: List[CrmRecord], shareTable: List[Share]): (Account, Search) => List[CrmRecord] =
  readContract.enforce(InMemoryCrm(records, shareTable).search)(shares.bind(shareTable))

@main def crmCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/crm"))
