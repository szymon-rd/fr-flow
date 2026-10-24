package rebac

import cats.effect.SyncIO
import com.sun.net.httpserver.{HttpExchange, HttpServer}
import frflow.*
import java.net.{InetSocketAddress, URLDecoder}
import java.nio.charset.StandardCharsets.UTF_8
import java.util.concurrent.atomic.AtomicReference

/** The service over HTTP, on localhost: one process holds the tuple store and the cache.
  *   GET  /check?tuple=doc:readme#viewer@user:ann[&at=V]  → yes or no (at the latest version unless `at` is given)
  *   POST /write?tuple=…  and  POST /delete?tuple=…       → the new version
  * Checks run CachedChecks' proven flow, through the cache, on the store's version; ServiceWiring governs this file.
  */
final class RebacService(schemaInForce: List[RelationDef], depth: List[Unit]):
  private val store = AtomicReference(TupleStore.empty)
  private val answers = LruCache.holding(Nil)

  /** One write or delete, applied to the store: the new version. */
  def write(w: Write): Int = synchronized(store.updateAndGet(_.write(w)).version)

  /** A check at a version (the latest if none is given, and never past the latest). */
  def check(q: Query, at: Option[Int]): Boolean =
    val s = store.get
    val v = at.fold(s.version)(_.min(s.version))
    knowledge.run[SyncIO](cachedChecks)(cache.bind(answers), schema.bind(schemaInForce), levels.bind(depth), writes.bind(s.writes))(
      Ask(q, v)).unsafeRunSync()

object RebacService:
  /** `kind:id#rel@kind:id`, `kind:id#rel@kind:id#rel` (a userset) or `kind:id#rel@>kind:id` (a link). */
  def parse(text: String): Option[RelTuple] =
    def obj(s: String) = s.split(":", 2) match
      case Array(k, i) if k.nonEmpty && i.nonEmpty => Some(Obj(k, i))
      case _                                     => None
    text.split("@", 2) match
      case Array(left, right) =>
        val subject: Option[Subject] =
          if right.startsWith(">") then obj(right.drop(1)).map(Subject.Link(_))
          else right.split("#", 2) match
            case Array(o, r) => obj(o).map(Subject.Members(_, r))
            case Array(p) if p.startsWith("user:") && p.length > 5 => Some(Subject.Person(p.drop(5)))
            case _ => None
        left.split("#", 2) match
          case Array(o, r) if r.nonEmpty => for { ob <- obj(o); s <- subject } yield RelTuple(ob, r, s)
          case _                         => None
      case _ => None

  def serve(port: Int, service: RebacService): HttpServer =
    val server = HttpServer.create(InetSocketAddress("127.0.0.1", port), 0)
    server.createContext("/", (ex: HttpExchange) =>
      val params = Option(ex.getRequestURI.getRawQuery).toList.flatMap(_.split("&")).flatMap(_.split("=", 2) match
        case Array(k, v) => Some(k -> URLDecoder.decode(v, UTF_8))
        case _           => None).toMap
      val (code, body) = (ex.getRequestMethod, ex.getRequestURI.getPath) match
        case ("GET", "/check") =>
          params.get("tuple").flatMap(parse) match
            case Some(RelTuple(o, r, Subject.Person(p))) =>
              (200, if service.check(Query(o, r, p), params.get("at").flatMap(_.toIntOption)) then "yes" else "no")
            case _ => (400, "check a tuple naming a user: doc:readme#viewer@user:ann")
        case ("POST", "/write" | "/delete") =>
          params.get("tuple").flatMap(parse) match
            case Some(t) => (200, service.write(if ex.getRequestURI.getPath == "/write" then Write.Add(t) else Write.Remove(t)).toString)
            case None    => (400, "a tuple: doc:readme#viewer@user:ann, doc:readme#viewer@group:eng#member, doc:readme#parent@>folder:eng")
        case _ => (404, "GET /check, POST /write, POST /delete")
      val bytes = (body + "\n").getBytes(UTF_8)
      ex.sendResponseHeaders(code, bytes.length)
      ex.getResponseBody.write(bytes)
      ex.close())
    server.start()
    server

/** `sbt "rebac/runMain rebac.rebacServer 8090"`: the service with the demo schema and OpenFGA's depth. */
object rebacServer:
  def main(args: Array[String]): Unit =
    val port = args.headOption.flatMap(_.toIntOption).getOrElse(8090)
    RebacService.serve(port, RebacService(demoSchema, serviceLevels))
    println(s"rebac on http://127.0.0.1:$port")
