package rebac

import frflow.*

// ============================================================================
// The HTTP layer: a boundary whose model is the protocol a client sees
// ============================================================================
// The protocol's parts below are functions building terms, written out in the model's Lean, not `define`s: a boundary's
// model cannot call a define (its Lean module would not import it).

/** A request's tuple, as parsed: none given, malformed (with the reason), or a tuple. */
enum Given:
  case Missing
  case Malformed(reason: String)
  case Tuple(t: RelTuple)
object Given extends Data[Given]

/** The version a check names: none (the latest), a number, or text that is not one. */
enum At:
  case Latest
  case Version(v: Int)
  case Invalid(text: String)
object At extends Data[At]

/** A request, as the routes read it (Server.scala). */
enum Request:
  case Check(t: Given, at: At)
  case Add(t: Given)
  case Delete(t: Given)
  case Unknown(method: String, path: String)
object Request extends Data[Request]

/** An answer: its status, the check's answer, and the version it was given at (a check's version, or the version a
  * write made); a refusal names the latest version and writes nothing.
  */
final case class Reply(status: Int, answer: Option[Boolean], version: Int)
object Reply extends Data[Reply]

/** What the HTTP layer works over: the schema it validates by, the log of writes, and the checks the check allows (in
  * production, CachedChecks answers them; in the layer's tests, this table does).
  */
final case class Served(schema: List[RelationDef], log: List[Write], allows: List[Ask])
object Served extends Data[Served]

/** What a client's request reaches. */
trait HttpApi:
  def handle(r: Term[Request]): Flow[Reply]

val http = Boundary[HttpApi]("http", "the service's HTTP layer: what a client's request is answered with")
// The boundary's operations are read by reflection, which finds a type's Lean only once it was derived: derive these.
private val protocolTypes = (summon[LeanType[Request]], summon[LeanType[Reply]], summon[LeanType[Served]])

/** Whether the schema declares the relation on the kind: as a relation it gives, or as the link a rule inherits through. */
private def declares(defs: Term[List[RelationDef]], kind: Term[String], rel: Term[String]): Term[Boolean] =
  defs.exists(d => d.kind === kind && (d.rel === rel ||
    d.rules.exists(r => r.on[Rule.Direct.type](False).on[Rule.Implied](_ => False).on[Rule.Inherited]((link, _) => link === rel))))

/** Whether a tuple may be written: its relation declared on its object's kind, and a userset's on the group's kind. */
private def fits(defs: Term[List[RelationDef]], t: Term[RelTuple]): Term[Boolean] =
  declares(defs, t.obj.kind, t.rel) && t.subject
    .on[Subject.Person](_ => True)
    .on[Subject.Members]((g, gr) => declares(defs, g.kind, gr))
    .on[Subject.Link](_ => True)

/** The version a check is answered at: the latest when none is named, a named one from 0 to the latest, else none. */
private def versionAsked(s: Term[Served], at: Term[At]): Term[Option[Int]] =
  at.on[At.Latest.type](some(s.log.length))
    .on[At.Version](v => (v >= 0 && v <= s.log.length).fold(some(v), none[Int]))
    .on[At.Invalid](_ => none[Int])

private def refused(s: Term[Served]): Term[Reply] = Reply(400, none[Boolean], s.log.length)

private def appended(s: Term[Served], g: Term[Given], w: Term[RelTuple] => Term[Write]): Term[Served] =
  g.on[Given.Tuple](t => fits(s.schema, t).fold(Served(s.schema, s.log ++ List(w(t)), s.allows), s))
    .on[Given.Missing.type](s)
    .on[Given.Malformed](_ => s)

/** What serving a request leaves: a write or a delete that fits is added to the log; nothing else changes. */
def afterRequest(s: Term[Served], r: Term[Request]): Term[Served] =
  r.on[Request.Check]((_, _) => s)
    .on[Request.Add](g => appended(s, g, t => Write[Write.Add](t)))
    .on[Request.Delete](g => appended(s, g, t => Write[Write.Remove](t)))
    .on[Request.Unknown]((_, _) => s)

private def changed(s: Term[Served], r: Term[Request], g: Term[Given]): Term[Reply] =
  g.on[Given.Tuple](t => fits(s.schema, t).fold(Reply(200, none[Boolean], afterRequest(s, r).log.length), refused(s)))
    .on[Given.Missing.type](refused(s))
    .on[Given.Malformed](_ => refused(s))

/** The answer to a request: a check of a person on a declared relation at a version it may name, with what the check
  * allows; a write or delete that fits, with the version it makes; a refusal (400) or an unknown path (404) else.
  */
def replyTo(s: Term[Served], r: Term[Request]): Term[Reply] =
  r.on[Request.Check]((g, at) =>
      g.on[Given.Tuple](t => t.subject
          .on[Subject.Person](p =>
            declares(s.schema, t.obj.kind, t.rel).fold(versionAsked(s, at)
              .fold(refused(s))(v => Reply(200, some(s.allows.contains(Ask(Query(t.obj, t.rel, p), v))), v)), refused(s)))
          .on[Subject.Members]((_, _) => refused(s))
          .on[Subject.Link](_ => refused(s)))
        .on[Given.Missing.type](refused(s))
        .on[Given.Malformed](_ => refused(s)))
    .on[Request.Add](g => changed(s, r, g))
    .on[Request.Delete](g => changed(s, r, g))
    .on[Request.Unknown]((_, _) => Reply(404, none[Boolean], s.log.length))

/** The protocol as the layer's tests see it. */
object HttpModel extends HttpApi, StateModel[Served]:
  def handle(r: Term[Request]) = state.get.flatMap(s => state.set(afterRequest(s, r)).map(_ => replyTo(s, r)))

val httpProtocol = Node.assumption(http)(HttpModel)("HttpProtocol",
  "A request is answered as the protocol says: a check of a person on a relation the schema declares, at a version from 0 to the latest (the latest when none is named), with what the check gives at that version and the version; a write or a delete of a tuple whose relations the schema declares, with the version it makes; anything else is refused (400), or not found (404), and writes nothing.",
  why = "Clients see the service through this layer; what a check answers is proven (CheckContract, CachedChecks), and this decides how a request reaches it. The layer (HttpLayer.scala) is the project's own code, tested against this model on generated runs of requests, with the check's answers given as a table: the test is of the layer alone, as the layer's answers are the check's in production (ServiceWiring).",
  idea = "Checks")
  .implementedBy(s => TableHttp(s), _.served)
