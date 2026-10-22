package crm

import com.sun.net.httpserver.{HttpExchange, HttpServer}
import java.net.InetSocketAddress
import java.nio.charset.StandardCharsets.UTF_8

/** The CRM over HTTP. Who calls is the account in the headers `X-User` and `X-Tenant` (authentication
  * is not modelled). Every request reaches the records through the read, deal or write side.
  *
  *   GET  /records?id=N | ?kind=Contact|Deal      records the caller may see (everything by default)
  *   GET  /deals                                  the sales screen
  *   POST /records  {"id":N,"kind":"Deal","title":"..."}   add a record of the caller's company
  *   POST /shares   {"record":N,"to":"globex","until":T?}  share a record (until a time, optionally)
  *   DELETE /shares?record=N&to=globex            unshare
  *
  * HttpApi governs this file.
  */
object CrmServer:
  def start(db: Db, port: Int): HttpServer =
    val server = HttpServer.create(InetSocketAddress("127.0.0.1", port), 0)
    val (read, deals) = (readSide(db), dealSide(db))
    server.createContext("/", (ex: HttpExchange) =>
      try
        val user = Account(Option(ex.getRequestHeaders.getFirst("X-User")).getOrElse(""), TenantId(Option(ex.getRequestHeaders.getFirst("X-Tenant")).getOrElse("")))
        val q = query(ex)
        (ex.getRequestMethod, ex.getRequestURI.getPath) match
          case ("GET", "/records") =>
            val s = q.get("id").map(i => Search.ById(BigInt(i))).orElse(q.get("kind").map(k => Search.OfKind(Kind.valueOf(k)))).getOrElse(Search.Everything)
            reply(ex, 200, json(read(user, s)))
          case ("GET", "/deals") => reply(ex, 200, json(deals(user, Search.Everything)))
          case ("POST", "/records") =>
            val b = body(ex)
            val r = CrmRecord(BigInt(field(b, "id")), user.tenant, Kind.valueOf(field(b, "kind")), field(b, "title"))
            changed(ex, writeTo(db, WriteCmd(user, Change.Add(r))).records.contains(r))
          case ("POST", "/shares") =>
            val b = body(ex)
            val sh = Share(BigInt(field(b, "record")), TenantId(field(b, "to")))
            val ok = writeTo(db, WriteCmd(user, Change.ShareWith(sh.record, sh.to))).shares.contains(sh)
            if ok then optional(b, "until").foreach(u => db.setExpiry(Expiry(sh.record, sh.to, BigInt(u))))
            changed(ex, ok)
          case ("DELETE", "/shares") =>
            changed(ex, !writeTo(db, WriteCmd(user, Change.Unshare(BigInt(q("record")), TenantId(q("to"))))).shares.contains(Share(BigInt(q("record")), TenantId(q("to")))))
          case _ => reply(ex, 404, "{\"error\":\"not found\"}")
      catch
        case e: frflow.ContractViolation => reply(ex, 500, s"{\"error\":${str(e.getMessage)}}")
        case e: Exception => reply(ex, 400, s"{\"error\":${str(String.valueOf(e.getMessage))}}")
    )
    server.start()
    server

  // A write its author's company may not make changes nothing: refused.
  private def changed(ex: HttpExchange, ok: Boolean) = if ok then reply(ex, 200, "{\"ok\":true}") else reply(ex, 403, "{\"error\":\"not yours to change\"}")
  private def query(ex: HttpExchange): Map[String, String] =
    Option(ex.getRequestURI.getRawQuery).toList.flatMap(_.split("&")).map(_.split("=", 2)).collect { case Array(k, v) => k -> java.net.URLDecoder.decode(v, UTF_8) }.toMap
  private def body(ex: HttpExchange) = String(ex.getRequestBody.readAllBytes(), UTF_8)
  private def optional(b: String, k: String): Option[String] =
    s""""$k"\\s*:\\s*("([^"]*)"|(-?\\d+))""".r.findFirstMatchIn(b).map(m => Option(m.group(2)).getOrElse(m.group(3)))
  private def field(b: String, k: String) = optional(b, k).getOrElse(throw IllegalArgumentException(s"missing $k"))
  private def str(s: String) = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\""
  private def json(rs: List[CrmRecord]) =
    rs.map(r => s"""{"id":${r.id},"tenant":${str(r.tenant.value)},"kind":${str(r.kind.toString)},"title":${str(r.title)}}""").mkString("[", ",", "]")
  private def reply(ex: HttpExchange, code: Int, s: String) =
    val b = s.getBytes(UTF_8)
    ex.getResponseHeaders.add("Content-Type", "application/json")
    ex.sendResponseHeaders(code, b.length)
    ex.getResponseBody.write(b); ex.close()

/** Serves the CRM: `sbt "crm/runMain crm.serveCrm crm.db 8080"`. */
@main def serveCrm(path: String, port: Int): Unit =
  val db = Db.open(path)
  startExpiryJob(db)
  CrmServer.start(db, port)
  println(s"CRM on http://127.0.0.1:$port (database $path)")
