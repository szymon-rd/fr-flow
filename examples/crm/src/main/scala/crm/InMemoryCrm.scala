package crm

/** The implementation: plain Scala, attached to `ReadContract` in Crm.scala. */
final class InMemoryCrm(records: List[CrmRecord], shareTable: List[Share]):
  def search(user: Account, query: Search): List[CrmRecord] =
    val sharedIds = shareTable.filter(_.to == user.tenant).map(_.record).toSet
    records
      .filter(r => r.tenant == user.tenant || sharedIds(r.id))
      .filter(r => query match
        case Search.ById(id)   => r.id == id
        case Search.OfKind(k)  => r.kind == k
        case Search.Everything => true)
