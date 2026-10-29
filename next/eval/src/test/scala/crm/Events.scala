package crm

/** The event log's rows: each event one line of fields, the first naming what it is (`Db.logEvent`). */
object Events:
  private val Sep = "\u001f"

  def text(e: Event): String = (e match
    case Event.Expired(now)         => List("expired", now.toString)
    case Event.Wrote(WriteCmd(by, c)) => List("wrote", by.email, by.tenant.value) ++ (c match
        case Change.Add(r)               => List("add", r.id.toString, r.tenant.value, r.kind.toString, r.title)
        case Change.ShareWith(id, to, u) => List("share", id.toString, to.value) ++ u.map(_.toString).toList
        case Change.Unshare(id, to)      => List("unshare", id.toString, to.value))).mkString(Sep)

  def read(line: String): Event = line.split(Sep, -1).toList match
    case List("expired", now)                 => Event.Expired(BigInt(now))
    case "wrote" :: email :: tenant :: change => Event.Wrote(WriteCmd(Account(email, TenantId(tenant)), change match
        case List("add", id, owner, kind, title) =>
          Change.Add(CrmRecord(BigInt(id), TenantId(owner), Kind.valueOf(kind), title))
        case "share" :: id :: to :: until => Change.ShareWith(BigInt(id), TenantId(to), until.headOption.map(BigInt(_)))
        case List("unshare", id, to)      => Change.Unshare(BigInt(id), TenantId(to))
        case other                        => throw IllegalStateException(s"not a change: $other")))
    case other => throw IllegalStateException(s"not an event: $other")
