package rebac

import frflow.*

/** What the HTTP layer answers requests over. RebacService is the running one; TableHttp's stands for it in tests. */
trait Backend:
  def schemaInForce: List[RelationDef]
  def latest: Int
  /** The check at a version from 0 to the latest. */
  def allowed(q: Query, v: Int): Boolean
  /** One write or delete: the version it makes. */
  def write(w: Write): Int

/** The HTTP layer: requests to replies, as HttpProtocol says, written in plain Scala; tested against HttpModel. */
class HttpLayer(backend: Backend) extends HttpApi:
  def handle(r: Term[Request]) = Flow.effect(r)(respond)

  def respond(r: Request): Reply = r match
    case Request.Check(Given.Tuple(RelTuple(o, rel, Subject.Person(p))), at) if declared(o.kind, rel) =>
      version(at).fold(refused)(v => Reply(200, Some(backend.allowed(Query(o, rel, p), v)), v))
    case Request.Add(Given.Tuple(t)) if fits(t)    => Reply(200, None, backend.write(Write.Add(t)))
    case Request.Delete(Given.Tuple(t)) if fits(t) => Reply(200, None, backend.write(Write.Remove(t)))
    case Request.Unknown(_, _)                     => Reply(404, None, backend.latest)
    case _                                         => refused

  /** Why a request is refused or not found, for the client. */
  def explain(r: Request): String =
    def tupleIssue(t: RelTuple): String =
      if !declared(t.obj.kind, t.rel) then s"the schema declares no relation ${t.rel} on ${t.obj.kind}"
      else t.subject match
        case Subject.Members(g, gr) if !declared(g.kind, gr) => s"the schema declares no relation $gr on ${g.kind}"
        case _ => "refused"
    def onTuple(g: Given)(ok: RelTuple => String): String = g match
      case Given.Missing       => "give a tuple: ?tuple=doc:readme#viewer@user:ann"
      case Given.Malformed(why) => why
      case Given.Tuple(t)      => ok(t)
    r match
      case Request.Check(g, at) => onTuple(g) {
        case RelTuple(_, _, Subject.Person(_)) if version(at).isEmpty => s"at must be a version from 0 to ${backend.latest}"
        case t @ RelTuple(_, _, Subject.Person(_)) => tupleIssue(t)
        case _ => "a check names a person: doc:readme#viewer@user:ann"
      }
      case Request.Add(g)        => onTuple(g)(tupleIssue)
      case Request.Delete(g)     => onTuple(g)(tupleIssue)
      case Request.Unknown(_, _) => "GET /check, POST /write, POST /delete"

  private def declared(kind: String, rel: String): Boolean =
    backend.schemaInForce.exists(d => d.kind == kind && (d.rel == rel || d.rules.exists {
      case Rule.Inherited(link, _) => link == rel
      case _                       => false
    }))
  private def fits(t: RelTuple): Boolean = declared(t.obj.kind, t.rel) && (t.subject match
    case Subject.Members(g, gr) => declared(g.kind, gr)
    case _                      => true)
  private def version(at: At): Option[Int] = at match
    case At.Latest      => Some(backend.latest)
    case At.Version(v)  => Option.when(v >= 0 && v <= backend.latest)(v)
    case At.Invalid(_)  => None
  private def refused = Reply(400, None, backend.latest)

/** The layer over a table of the check's answers and a log in memory: what it is tested against HttpModel with. */
final class TableHttp private (table: TableHttp.Table) extends HttpLayer(table):
  def served: Served = table.served
object TableHttp:
  def apply(start: Served): TableHttp = new TableHttp(Table(start))
  final class Table(start: Served) extends Backend:
    private var log = start.log
    def served: Served = Served(start.schema, log, start.allows)
    def schemaInForce = start.schema
    def latest = log.size
    def allowed(q: Query, v: Int) = start.allows.contains(Ask(q, v))
    def write(w: Write) = { log = log :+ w; log.size }
